"""Coverage checks for scalar functions with ordinary recursive calls."""
import ast
import re
from dataclasses import dataclass
from pathlib import Path
from lang.py.global_inputs import GlobalInputError, function_globals, annotation_kind, needs_heap_globals
from lang.py.imports import bindings
from lang.py.permutation_support import permutation_binding, permutation_arguments
from lang.py.defaults import literal_default
from lang.py.named_callbacks import callback_bindings_valid, callback_signature
from lang.py.memo_support import cache_decorator, uses_memoized
from lang.py.call_graph import call_targets
from lang.py.sorting_support import uses_sort_model
from lang.py.tuple_support import flat_unpacking, unpacked_tuple_displays, unpacked_return_tuple_displays, compared_set_tuple_displays, compared_local_tuple_displays, runtime_tuple_element
from lang.py.class_support import ordinary_attribute, plain_class_methods


# These builtin constructors preserve positional arguments without the special
# normalization performed by OSError and the Unicode error constructors.
PLAIN_EXCEPTIONS = frozenset({
    'BaseException', 'Exception', 'ArithmeticError', 'AssertionError',
    'AttributeError', 'EOFError', 'IndexError', 'KeyError', 'LookupError',
    'NotImplementedError', 'OverflowError', 'RuntimeError', 'StopIteration',
    'TypeError', 'ValueError', 'ZeroDivisionError',
})


def plain_fstring(node):
    """Check formatting options whose scalar semantics are exactly str(value)."""
    return isinstance(node, ast.JoinedStr) and all(
        isinstance(part, ast.Constant) and type(part.value) is str
        or isinstance(part, ast.FormattedValue) and part.conversion in (-1, ord('s'))
        and (part.format_spec is None
             or isinstance(part.format_spec, ast.JoinedStr) and not part.format_spec.values)
        for part in node.values)


def integer_instance(node):
    """Recognize the restricted builtin type test without evaluating classinfo."""
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'isinstance' and len(node.args) == 2 and not node.keywords
            and isinstance(node.args[1], ast.Name) and node.args[1].id == 'int')


@dataclass(frozen=True)
class RangeSum:
    name: str
    element: ast.expr
    bounds: list[ast.expr]
    conditions: list[ast.expr]


def range_sum(node):
    """Normalize builtin range sums without executing or rewriting the source AST."""
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'sum' and len(node.args) == 1 and not node.keywords):
        return None
    iterable = node.args[0]
    if isinstance(iterable, ast.GeneratorExp):
        if len(iterable.generators) != 1:
            return None
        loop = iterable.generators[0]
        if not isinstance(loop.target, ast.Name) or loop.is_async:
            return None
        name, element, conditions = loop.target.id, iterable.elt, loop.ifs
        iterable = loop.iter
    else:
        # The private binder cannot collide with any Python source identifier.
        name, element, conditions = '', ast.Name(id='', ctx=ast.Load()), []
    if not (isinstance(iterable, ast.Call) and isinstance(iterable.func, ast.Name)
            and iterable.func.id == 'range' and 1 <= len(iterable.args) <= 3
            and not iterable.keywords):
        return None
    return RangeSum(name, element, iterable.args, conditions)


@dataclass(frozen=True)
class RangeExtremum:
    maximum: bool
    bounds: list[ast.expr]
    key: str


def range_extremum(node):
    """Recognize min/max of a range with a named, source-checked key function."""
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id in ('min', 'max') and len(node.args) == 1
            and len(node.keywords) == 1 and node.keywords[0].arg == 'key'
            and isinstance(node.keywords[0].value, ast.Name)):
        return None
    iterable = node.args[0]
    if not (isinstance(iterable, ast.Call) and isinstance(iterable.func, ast.Name)
            and iterable.func.id == 'range' and 1 <= len(iterable.args) <= 3
            and not iterable.keywords):
        return None
    return RangeExtremum(node.func.id == 'max', iterable.args, node.keywords[0].value.id)


@dataclass(frozen=True)
class SequenceExtremum:
    maximum: bool
    iterable: ast.expr
    parameter: str
    key: ast.expr


def sequence_extremum(node):
    """Recognize an immediately consumed, nonescaping sequence-key callback."""
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id in ('min', 'max') and len(node.args) == 1
            and len(node.keywords) == 1 and node.keywords[0].arg == 'key'):
        return None
    if range_extremum(node) is not None:
        return None
    key = node.keywords[0].value
    if isinstance(key, ast.Name):
        parameter = '$formalsw.extremum'
        body = ast.Call(func=key, args=[ast.Name(id=parameter, ctx=ast.Load())], keywords=[])
        ast.copy_location(body, node)
        ast.fix_missing_locations(body)
    elif (isinstance(key, ast.Lambda) and len(key.args.args) == 1
          and not key.args.posonlyargs and not key.args.kwonlyargs
          and not key.args.vararg and not key.args.kwarg
          and not key.args.defaults and not key.args.kw_defaults):
        parameter, body = key.args.args[0].arg, key.body
    else:
        return None
    return SequenceExtremum(node.func.id == 'max', node.args[0], parameter, body)



@dataclass(frozen=True)
class SequenceSort:
    iterable: ast.expr
    parameter: str
    key: ast.expr
    reverse: ast.expr


def sequence_sort(node):
    """Recognize stable sorting with an immediately consumed unary key callback."""
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'sorted' and len(node.args) == 1
            and 1 <= len(node.keywords) <= 2):
        return None
    names = [keyword.arg for keyword in node.keywords]
    if len(set(names)) != len(names) or 'key' not in names or set(names) - {'key', 'reverse'}:
        return None
    key = next(keyword.value for keyword in node.keywords if keyword.arg == 'key')
    if isinstance(key, ast.Name):
        parameter = '$formalsw.sorted.item'
        body = ast.Call(func=key, args=[ast.Name(id=parameter, ctx=ast.Load())], keywords=[])
        ast.copy_location(body, node)
        ast.fix_missing_locations(body)
    elif (isinstance(key, ast.Lambda) and len(key.args.args) == 1
          and not key.args.posonlyargs and not key.args.kwonlyargs
          and not key.args.vararg and not key.args.kwarg
          and not key.args.defaults and not key.args.kw_defaults):
        parameter, body = key.args.args[0].arg, key.body
    else:
        return None
    reverse = next((keyword.value for keyword in node.keywords if keyword.arg == 'reverse'),
                   ast.Constant(value=False))
    return SequenceSort(node.args[0], parameter, body, reverse)


def zip_iterable(node, module):
    """Recognize the builtin only where its iterator is immediately consumed."""
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'zip' and not bindings(module, 'zip'))


def enumerate_arguments(node):
    """Normalize a fresh enumerate iterator, preserving argument evaluation order."""
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'enumerate'):
        return None
    if len(node.args) in (1, 2) and not node.keywords:
        return [node.args[0], node.args[1] if len(node.args) == 2 else ast.Constant(value=0)]
    if len(node.args) == 1 and len(node.keywords) == 1 and node.keywords[0].arg == 'start':
        return [node.args[0], node.keywords[0].value]
    return None


def reversed_sequence(node, module):
    """Recognize a fresh reverse iterator consumed directly by a for loop."""
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'reversed' and not bindings(module, 'reversed'))


def sequence_sum(node):
    """Recognize a consumed iterable or generator, retaining the optional start."""
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'sum' and range_sum(node) is None):
        return None
    if len(node.args) in (1, 2) and not node.keywords:
        iterable, start = node.args[0], node.args[1] if len(node.args) == 2 else ast.Constant(value=0)
    elif len(node.args) == 1 and len(node.keywords) == 1 and node.keywords[0].arg == 'start':
        iterable, start = node.args[0], node.keywords[0].value
    else:
        return None
    if (isinstance(iterable, ast.Call) and isinstance(iterable.func, ast.Name)
            and iterable.func.id == 'range'):
        # A range is constructed before the start expression, just as the
        # first iterator of an immediately consumed generator is constructed.
        iterable = ast.copy_location(ast.GeneratorExp(
            elt=ast.Name(id='', ctx=ast.Load()), generators=[ast.comprehension(
                target=ast.Name(id='', ctx=ast.Store()), iter=iterable, ifs=[], is_async=0)]), iterable)
    return iterable, start


def materialized_range(node):
    """Lower list(range(...)) to a private range comprehension."""
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'list' and len(node.args) == 1 and not node.keywords):
        return None
    iterable = node.args[0]
    if not (isinstance(iterable, ast.Call) and isinstance(iterable.func, ast.Name)
            and iterable.func.id == 'range'):
        return None
    name = '$formalsw.range.item'
    return ast.copy_location(ast.ListComp(
        elt=ast.Name(id=name, ctx=ast.Load()),
        generators=[ast.comprehension(target=ast.Name(id=name, ctx=ast.Store()),
                                      iter=iterable, ifs=[], is_async=0)]), node)


def mapped_list(node):
    """Lower an immediately materialized unary builtin map to its private iterator."""
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'list'
            and len(node.args) == 1 and not node.keywords):
        return None
    mapped = node.args[0]
    if not (isinstance(mapped, ast.Call) and isinstance(mapped.func, ast.Name) and mapped.func.id == 'map'
            and len(mapped.args) == 2 and not mapped.keywords
            and isinstance(mapped.args[0], ast.Name) and mapped.args[0].id in ('int', 'str', 'ord', 'len')):
        return None
    name = '$formalsw.map.item'
    generator = ast.GeneratorExp(
        elt=ast.Call(func=mapped.args[0], args=[ast.Name(id=name, ctx=ast.Load())], keywords=[]),
        generators=[ast.comprehension(target=ast.Name(id=name, ctx=ast.Store()),
                                      iter=mapped.args[1], ifs=[], is_async=0)])
    return ast.copy_location(ast.Call(func=node.func, args=[generator], keywords=[]), node)


def reverse_keyword(node):
    """Recognize one explicit keyword without conflating it with positional arguments."""
    if (isinstance(node, ast.Call) and len(node.keywords) == 1
            and node.keywords[0].arg == 'reverse'):
        return node.keywords[0].value
    return None


def consumed_generator(node):
    """Recognize immediate consumers without materializing their lazy input."""
    if not (isinstance(node, ast.Call) and len(node.args) == 1):
        return None
    if node.keywords:
        reverse = reverse_keyword(node)
        if not (isinstance(node.func, ast.Name) and node.func.id == 'sorted'
                and isinstance(reverse, ast.Constant) and type(reverse.value) is bool):
            return None
    iterable = node.args[0]
    if (isinstance(node.func, ast.Name) and node.func.id in ('all', 'any')
            and isinstance(iterable, ast.Call) and isinstance(iterable.func, ast.Name)
            and iterable.func.id == 'range'):
        name = '$formalsw.truth.item'
        iterable = ast.copy_location(ast.GeneratorExp(
            elt=ast.Name(id=name, ctx=ast.Load()), generators=[ast.comprehension(
                target=ast.Name(id=name, ctx=ast.Store()), iter=iterable, ifs=[], is_async=0)]), iterable)
    if (isinstance(iterable, ast.GeneratorExp)
            and (isinstance(node.func, ast.Name) and node.func.id in ('list', 'sorted', 'all', 'any')
                 or isinstance(node.func, ast.Attribute) and node.func.attr == 'join')):
        return node.func, iterable
    return None


def reversed_list(node):
    """Recognize the eager builtin composition without exposing an iterator."""
    if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'list' and len(node.args) == 1 and not node.keywords):
        inner = node.args[0]
        if (isinstance(inner, ast.Call) and isinstance(inner.func, ast.Name)
                and inner.func.id == 'reversed' and len(inner.args) == 1 and not inner.keywords):
            return inner.args[0]
    return None


def library_functions(module):
    """Supported standard-library functions, preserving their import bindings."""
    functions = {alias.asname or alias.name: (node.module, alias.name, node)
            for node in module.body if isinstance(node, ast.ImportFrom)
            and node.level == 0 and node.module == 'math'
            for alias in node.names if alias.name in ('isqrt', 'gcd', 'comb', 'factorial')}
    for node in module.body:
        if isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name == 'math':
                    for name in ('isqrt', 'gcd', 'comb', 'factorial'):
                        functions[f'{alias.asname or alias.name}.{name}'] = ('math', name, node)
    return functions


def library_name(node):
    """Names of directly imported functions or attributes of imported modules."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
        return f'{node.value.id}.{node.attr}'
    return None


def uses_library_calls(module, function):
    """Follow local helpers to library calls that require the call interpreters."""
    libraries = library_functions(module)
    functions = {node.name: node for node in module.body if isinstance(node, ast.FunctionDef)}
    pending, visited = [function], set()
    while pending:
        current = pending.pop()
        if current.name in visited:
            continue
        visited.add(current.name)
        for statement in current.body:
            for node in ast.walk(statement):
                if isinstance(node, ast.Call):
                    if library_name(node.func) in libraries:
                        return True
                    if isinstance(node.func, ast.Name) and node.func.id in functions:
                        pending.append(functions[node.func.id])
    return False


def uses_builtin(module, function, name):
    """Find an unshadowed builtin in the reachable local function bodies."""
    if bindings(module, name):
        return False
    functions = {node.name: node for node in module.body if isinstance(node, ast.FunctionDef)}
    pending, visited = [function], set()
    while pending:
        current = pending.pop()
        if current.name in visited:
            continue
        visited.add(current.name)
        for node in (part for statement in current.body for part in ast.walk(statement)):
            for target in call_targets(node):
                if target == name:
                    return True
                if target in functions:
                    pending.append(functions[target])
    return False


def uses_method(module, function, name):
    """Find a method call in the reachable local function bodies."""
    functions = {node.name: node for node in module.body if isinstance(node, ast.FunctionDef)}
    pending, visited = [function], set()
    while pending:
        current = pending.pop()
        if current.name in visited:
            continue
        visited.add(current.name)
        for node in (part for statement in current.body for part in ast.walk(statement)):
            if isinstance(node, ast.Call):
                if isinstance(node.func, ast.Attribute) and node.func.attr == name:
                    return True
                pending.extend(functions[target] for target in call_targets(node) if target in functions)
    return False


def _uses_syntax(module, function, predicate):
    """Search function bodies and their local callees without following cycles."""
    functions = {node.name: node for node in module.body if isinstance(node, ast.FunctionDef)}
    pending, visited = [function], set()
    while pending:
        current = pending.pop()
        if current.name in visited:
            continue
        visited.add(current.name)
        for statement in current.body:
            for node in ast.walk(statement):
                if predicate(node):
                    return True
                pending.extend(functions[target] for target in call_targets(node) if target in functions)
    return False


def uses_bytes(module, function):
    return _uses_syntax(module, function,
                        lambda node: isinstance(node, ast.Constant) and type(node.value) is bytes)


def uses_assertions(module, function):
    return _uses_syntax(module, function, lambda node: isinstance(node, ast.Assert))


def general_division(node):
    """Use the call interpreter for divisors outside the legacy literal subset."""
    if isinstance(node, ast.BinOp):
        divisor = node.right
    elif isinstance(node, ast.AugAssign):
        divisor = node.value
    else:
        return False
    return (isinstance(node.op, (ast.FloorDiv, ast.Mod))
            and not (isinstance(divisor, ast.Constant) and type(divisor.value) is int and divisor.value >= 0))


def identity_comparison(node):
    return (isinstance(node, ast.Compare) and len(node.ops) == 1
            and isinstance(node.ops[0], (ast.Is, ast.IsNot)))


def singleton_literal(node):
    return isinstance(node, ast.Constant) and (node.value is None or type(node.value) is bool)


def has_partial_primitives(module, function):
    """Follow local callees to operations that need a runtime coverage proof."""
    if uses_memoized(module, function):
        # Integer-only cache keys are partial on other scalar values. Every
        # contract must also establish coverage, especially equivalence claims.
        return True
    byte_values = uses_bytes(module, function)
    functions = {node.name: node for node in module.body if isinstance(node, ast.FunctionDef)}
    pending = [function]
    visited = set()
    while pending:
        current = pending.pop()
        if current.name in visited:
            continue
        visited.add(current.name)
        for node in ast.walk(current):
            if identity_comparison(node) and not any(map(singleton_literal, [node.left, *node.comparators])):
                return True
            if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                    and node.func.id in ('int', 'pow') and not bindings(module, node.func.id)):
                return True
            if isinstance(node, (ast.BinOp, ast.AugAssign)) and isinstance(node.op, ast.Pow):
                return True
            if byte_values and isinstance(node, (ast.BinOp, ast.AugAssign)) and isinstance(node.op, ast.Mod):
                return True
            pending.extend(functions[target] for target in call_targets(node) if target in functions)
    return False



def uses_set_iteration(module, function):
    """
    Select arbitrary-order execution when a reachable loop may consume a set.

    This is conservative backend selection, not permission to execute unknown
    constructs: the source checker and universal Supported obligation still apply.
    Unsupported consumers still require their own execution coverage proof.
    """
    if module is None:
        return False
    functions = {node.name: node for node in module.body if isinstance(node, ast.FunctionDef)}
    pending, visited = [function], set()
    sets, loops = False, False
    while pending:
        current = pending.pop()
        if current.name in visited:
            continue
        visited.add(current.name)
        kinds = [annotation_kind(arg.annotation) for arg in callback_signature(module, current)]
        kinds.append(annotation_kind(current.returns))
        sets |= any(kind and (kind == 'set' or kind.startswith('set[')) for kind in kinds)
        for statement in current.body:
            for node in ast.walk(statement):
                sets |= isinstance(node, (ast.Set, ast.SetComp))
                if isinstance(node, ast.For):
                    loops |= not (isinstance(node.iter, ast.Call) and isinstance(node.iter.func, ast.Name)
                                  and node.iter.func.id == 'range')
                loops |= (sequence_extremum(node) is not None or sequence_sort(node) is not None
                          or sequence_sum(node) is not None)
                if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                    sets |= node.func.id == 'set' and not bindings(module, 'set')
                    pending.extend(functions[target] for target in call_targets(node) if target in functions)
        if sets and loops:
            return True
    return False


def uses_heap_calls(module, function):
    """Find list allocation or use in the transitive local call graph."""
    if needs_heap_globals(module, function):
        return True
    if _uses_syntax(module, function, lambda node: isinstance(node, ast.Compare)
                    and any(isinstance(op, (ast.In, ast.NotIn)) for op in node.ops)):
        return True
    functions = {node.name: node for node in module.body if isinstance(node, ast.FunctionDef)}
    classes = {node.name for node in module.body if isinstance(node, ast.ClassDef)}
    pending, visited = [function], set()
    while pending:
        current = pending.pop()
        if current.name in visited:
            continue
        visited.add(current.name)
        kinds = [annotation_kind(arg.annotation) for arg in callback_signature(module, current)]
        kinds.append(annotation_kind(current.returns))
        if getattr(current, 'formalsw_callback_origin', None) and any(
                isinstance(arg.annotation, ast.Name) and arg.annotation.id in classes
                for arg in callback_signature(module, current)):
            return True
        if any(kind and (kind.startswith(('list[', 'tuple[', 'set[', 'dict[')) or kind in ('bytearray', 'record')) for kind in kinds):
            return True
        # Defaults are evaluated at definition time, outside the modeled body.
        # Their validation must not select a different execution backend.
        parts = [part for statement in current.body for part in ast.walk(statement)]
        # Existing scalar tuple swaps do not allocate a first-class tuple in that
        # backend. Other tuple expressions need shared-reference execution.
        scalar_displays = {id(node.value) for node in parts
                           if isinstance(node, ast.Assign) and len(node.targets) == 1
                           and isinstance(node.targets[0], ast.Tuple) and isinstance(node.value, ast.Tuple)
                           and len(node.targets[0].elts) == len(node.value.elts)
                           and all(isinstance(target, ast.Name) for target in node.targets[0].elts)}
        for node in parts:
            if (isinstance(node, (ast.List, ast.Set, ast.ListComp, ast.SetComp, ast.Dict)) or reversed_list(node) is not None
                    or sequence_extremum(node) is not None or sequence_sort(node) is not None
                    or sequence_sum(node) is not None and not bindings(module, "sum")
                    or isinstance(node, ast.Tuple) and isinstance(node.ctx, ast.Load) and id(node) not in scalar_displays
                    or isinstance(node, ast.For) and not (isinstance(node.iter, ast.Call)
                        and isinstance(node.iter.func, ast.Name) and node.iter.func.id == 'range')
                    or isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in classes | {"bytearray", "list", "tuple", "set", "sorted", "all", "any"}
                    or isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                    and node.func.id == "divmod" and not bindings(module, "divmod")
                    or isinstance(node, ast.Attribute) and node.attr in ('append', 'add', 'get', 'setdefault', 'pop', 'count', 'join', 'replace', 'zfill', 'sort', 'strip', 'split')):
                return True
            pending.extend(functions[target] for target in call_targets(node) if target in functions)
    return False


def uses_parallel_model(function: ast.FunctionDef) -> bool:
    """Select the concurrent interpreter without imposing a particular signature."""
    return (any(isinstance(arg.annotation, ast.Name) and arg.annotation.id == 'Lock'
                for arg in function.args.args)
            or bool(re.search(r'\bParallel\(', ast.get_docstring(function, clean=False) or '')))


def uses_calls_model(module, function):
    if (uses_parallel_model(function) or uses_sort_model(module, function)
            or any(annotation_kind(arg.annotation) is None for arg in function.args.args)):
        return False
    if uses_memoized(module, function):
        return True
    if needs_heap_globals(module, function):
        return True
    try:
        if function_globals(module, function):
            return False
    except GlobalInputError:
        return False
    names = {node.name for node in module.body if isinstance(node, ast.FunctionDef)}
    names.update(library_functions(module))
    if (any(annotation_kind(arg.annotation) == 'bytes' for arg in function.args.args)
            or function.args.defaults or uses_heap_calls(module, function)
            or any(uses_method(module, function, method) for method in ("bit_length", "bit_count"))):
        return True
    return any(
        isinstance(node, (ast.BoolOp, ast.IfExp, ast.GeneratorExp, ast.Break, ast.Continue, ast.Subscript, ast.Assert, ast.JoinedStr, ast.AnnAssign))
        or isinstance(node, ast.Constant) and type(node.value) is bytes
        or range_sum(node) is not None
        or general_division(node)
        or identity_comparison(node)
        or isinstance(node, (ast.BinOp, ast.AugAssign)) and isinstance(node.op, (ast.Pow, ast.BitAnd, ast.BitOr, ast.BitXor, ast.LShift, ast.RShift))
        or isinstance(node, ast.Assign) and any(isinstance(target, ast.Tuple) for target in node.targets)
        or isinstance(node, ast.Call) and library_name(node.func) in names | {'bool', 'int', 'str', 'bin', 'ord', 'abs', 'pow', 'max', 'min', 'len', 'isinstance'}
        or isinstance(node, ast.For) and isinstance(node.iter, ast.Call)
        and isinstance(node.iter.func, ast.Name) and node.iter.func.id == 'range' and len(node.iter.args) != 1
        for node in ast.walk(function)
    )


def check_calls(module, function, reject, *, heap=False):
    entry_function = function
    functions = {node.name: node for node in module.body if isinstance(node, ast.FunctionDef)}
    classes = {node.name: node for node in module.body if isinstance(node, ast.ClassDef)}
    libraries = library_functions(module)
    visited = set()
    visited_classes = set()
    return_tuples = unpacked_return_tuple_displays(module, function) if heap else set()
    memoized_execution = uses_memoized(module, function)
    if memoized_execution and uses_set_iteration(module, function):
        reject(function, 'set traversal and memoized calls need a combined execution model')

    def visit_class(cls):
        if cls.name in visited_classes:
            return
        visited_classes.add(cls.name)
        for method in plain_class_methods(module, cls, reject):
            visit(method, cls)

    def visit(function, owner=None):
        if id(function) in visited:
            return
        visited.add(id(function))
        if hasattr(function, "formalsw_local_function_error"):
            reject(function, function.formalsw_local_function_error)
        if not callback_bindings_valid(module, function):
            reject(function, 'named callbacks require protected module-level function bindings')
        if owner is None and sum(isinstance(node, ast.FunctionDef) and node.name == function.name
               for node in module.body) != 1:
            reject(function, 'call targets must have one module-level definition')
        for node in module.body if owner is None else ():
            if isinstance(node, ast.FunctionDef):
                continue
            for item in ast.walk(node):
                if (isinstance(item, ast.Name) and isinstance(item.ctx, (ast.Store, ast.Del))
                        and item.id == function.name
                        or isinstance(item, ast.Attribute) and isinstance(item.ctx, (ast.Store, ast.Del))
                        and isinstance(item.value, ast.Name) and item.value.id == function.name
                        or isinstance(item, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef))
                        and item.name == function.name
                        or isinstance(item, (ast.Import, ast.ImportFrom)) and any(
                            (alias.asname or alias.name.split('.')[0]) in (function.name, '*')
                            for alias in item.names)):
                    reject(item, 'module-level call targets must not be rebound')
        cached = cache_decorator(module, function)
        if cached and heap:
            if not memoized_execution:
                reject(function, 'cached helpers reached through methods require cache-aware call discovery')
            # Cache entries run in the scalar interpreter. Validate the whole
            # dependency graph there, even when another caller uses the heap.
            check_calls(module, function, reject, heap=False)
            return
        if uses_parallel_model(function):
            reject(function, 'call execution does not support parallel workers')
        if cached and (function.args.defaults or any(annotation_kind(arg.annotation) != 'int'
                                                   for arg in function.args.args)):
            reject(function, 'memoized functions require integer positional arguments without defaults')
        if function.decorator_list and not cached or getattr(function, 'type_params', []) or function.args.posonlyargs or \
                function.args.kwonlyargs or function.args.vararg or function.args.kwarg:
            reject(function, 'call execution requires undecorated plain positional functions')
        for default in function.args.defaults:
            try:
                literal_default(default)
            except ValueError as error:
                reject(default, str(error))
        locals_ = {arg.arg for arg in function.args.args}
        # Comprehension targets have their own scope and must not leak into the
        # enclosing function's locals (including before the expression).
        def stored_names(node):
            if isinstance(node, (ast.GeneratorExp, ast.ListComp, ast.SetComp, ast.DictComp)):
                return set()
            if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store):
                return {node.id}
            return set().union(*(stored_names(child) for child in ast.iter_child_nodes(node)))
        locals_.update(stored_names(function))
        globals_ = set()
        try:
            global_inputs = function_globals(module, function, heap_calls=heap)
            if global_inputs and not heap:
                reject(function, 'global inputs require heap call execution')
            globals_.update(item.name for item in global_inputs)
        except GlobalInputError as error:
            reject(function, str(error))
        hidden_tuples = (unpacked_tuple_displays(function) | return_tuples
                         | compared_set_tuple_displays(function)
                         | compared_local_tuple_displays(module, function)) if heap else set()
        # A local may reuse a function/class name as data. Each call site below
        # separately rejects invoking a shadowed module-level target.
        for index, arg in enumerate(callback_signature(module, function)):
            if getattr(arg, "formalsw_capture", False):
                continue
            if owner is not None and index == 0:
                continue
            if heap and isinstance(arg.annotation, ast.Name) and arg.annotation.id in classes:
                visit_class(classes[arg.annotation.id])
                continue
            # Only the entry signature defines a quantified contract domain.
            # Helper annotations do not constrain Python call arguments.
            if function is not entry_function:
                continue
            kind = annotation_kind(arg.annotation)
            if kind not in ('int', 'str', 'bytes', 'bool') and not (heap and kind and (kind.startswith(('list[', 'tuple[', 'set[', 'dict[')) or kind in ('bytes', 'bytearray'))):
                reject(arg, 'call arguments require scalar annotations or supported heap list annotations' if heap
                       else 'call arguments require scalar int, str, or bool annotations')

        def expr(node, scope=None):
            scope = locals_ if scope is None else scope
            recurse = lambda child: expr(child, scope)
            materialized = materialized_range(node)
            if materialized is not None:
                if not heap:
                    reject(node, 'materialized ranges require heap call execution')
                for builtin in ('list', 'range'):
                    if builtin in scope or bindings(module, builtin):
                        reject(node, f'materialized ranges require the unshadowed builtin {builtin}')
                expr(materialized, scope)
                return
            mapped = mapped_list(node)
            if mapped is not None:
                if not heap:
                    reject(node, 'materialized maps require heap call execution')
                for builtin in ('list', 'map', node.args[0].args[0].id):
                    if builtin in scope or bindings(module, builtin):
                        reject(node, f'materialized map requires the unshadowed builtin {builtin}')
                expr(mapped, scope)
                return
            sorting = sequence_sort(node)
            if sorting is not None:
                if not heap:
                    reject(node, 'sorting with a key requires heap call execution')
                if 'sorted' in scope or bindings(module, 'sorted'):
                    reject(node, 'sorting requires the unshadowed builtin sorted')
                if isinstance(sorting.iterable, ast.GeneratorExp):
                    reject(sorting.iterable, 'sorting a generator with a key is unsupported')
                    return
                recurse(sorting.iterable)
                recurse(sorting.reverse)
                expr(sorting.key, scope | {sorting.parameter})
                return
            sequence = sequence_extremum(node)
            if sequence is not None:
                if not heap:
                    reject(node, 'sequence extrema with keys require heap call execution')
                if node.func.id in scope or bindings(module, node.func.id):
                    reject(node, 'sequence extrema require the unshadowed builtin min/max')
                recurse(sequence.iterable)
                expr(sequence.key, scope | {sequence.parameter})
                return
            extremum = range_extremum(node)
            if extremum is not None:
                if heap:
                    reject(node, 'range extrema with key currently require scalar call execution')
                for builtin in (node.func.id, 'range'):
                    if builtin in scope or bindings(module, builtin):
                        reject(node, f'range extrema require the unshadowed builtin {builtin}')
                if extremum.key in scope or extremum.key not in functions:
                    reject(node, 'range extrema require an unshadowed module-level key function')
                else:
                    visit(functions[extremum.key])
                for bound in extremum.bounds:
                    recurse(bound)
                return
            if heap and isinstance(node, (ast.ListComp, ast.SetComp)):
                if any(generator.is_async or not (isinstance(generator.target, ast.Name) or flat_unpacking(generator.target))
                       for generator in node.generators):
                    reject(node, 'comprehensions require synchronous loops with names or flat tuple/list targets')
                    return
                inner_scope = scope | {target.id for generator in node.generators
                                       for target in ast.walk(generator.target) if isinstance(target, ast.Name)}
                for index, generator in enumerate(node.generators):
                    iterable_scope = scope if index == 0 else inner_scope
                    iterable = generator.iter
                    if (isinstance(iterable, ast.Call) and isinstance(iterable.func, ast.Name)
                            and iterable.func.id == 'range'):
                        if 'range' in iterable_scope or bindings(module, 'range'):
                            reject(iterable, 'comprehensions require the unshadowed builtin range')
                        if not 1 <= len(iterable.args) <= 3 or iterable.keywords:
                            reject(iterable, 'range requires one to three positional arguments')
                        for argument in iterable.args:
                            expr(argument, iterable_scope)
                    elif (isinstance(iterable, ast.Call) and isinstance(iterable.func, ast.Name)
                          and iterable.func.id == 'enumerate'):
                        if 'enumerate' in iterable_scope or bindings(module, 'enumerate'):
                            reject(iterable, 'enumerate iteration requires the unshadowed builtin enumerate')
                        if not flat_unpacking(generator.target) or len(generator.target.elts) != 2:
                            reject(generator.target, 'enumerate requires immediate unpacking into two local names')
                        arguments = enumerate_arguments(iterable)
                        if arguments is None:
                            reject(iterable, 'enumerate supports an iterable and optional positional or keyword start')
                        else:
                            for argument in arguments:
                                expr(argument, iterable_scope)
                    elif permutation_binding(iterable, module) is not None:
                        name = permutation_binding(iterable, module)
                        if name in iterable_scope:
                            reject(iterable, 'permutations requires an unshadowed standard-library import')
                        arguments = permutation_arguments(iterable, module)
                        if arguments is None:
                            reject(iterable, 'permutations requires a positional iterable and optional length')
                        else:
                            for argument in arguments:
                                if isinstance(argument, ast.Tuple):
                                    hidden_tuples.add(argument)
                                expr(argument, iterable_scope)
                    elif zip_iterable(iterable, module):
                        if 'zip' in iterable_scope:
                            reject(iterable, 'zip iteration requires the unshadowed builtin zip')
                        if iterable.keywords:
                            reject(iterable, 'zip iteration supports positional sequence arguments, without strict')
                        for argument in iterable.args:
                            # The sequence tuple itself cannot escape its private zip iterator.
                            if isinstance(argument, ast.Tuple):
                                hidden_tuples.add(argument)
                            expr(argument, iterable_scope)
                    else:
                        expr(iterable, iterable_scope)
                    for condition in generator.ifs:
                        expr(condition, inner_scope)
                expr(node.elt, inner_scope)
                return
            consumed = consumed_generator(node)
            if consumed is not None:
                if not heap:
                    reject(node, 'generator consumption requires heap call execution')
                    return
                consumer, generator = consumed
                if isinstance(consumer, ast.Name):
                    if consumer.id in scope or bindings(module, consumer.id):
                        reject(node, f'generator consumption requires the unshadowed builtin {consumer.id}')
                else:
                    ordinary_attribute(consumer, reject)
                    recurse(consumer.value)
                recurse(ast.copy_location(ast.ListComp(elt=generator.elt, generators=generator.generators), generator))
                return
            summed = sequence_sum(node)
            if summed is not None and not bindings(module, "sum"):
                if not heap:
                    reject(node, 'sequence sums require heap call execution')
                    return
                if 'sum' in scope:
                    reject(node, 'sums require the unshadowed builtin sum')
                iterable, start = summed
                if isinstance(iterable, ast.GeneratorExp):
                    recurse(ast.copy_location(ast.ListComp(elt=iterable.elt, generators=iterable.generators), iterable))
                else:
                    recurse(iterable)
                recurse(start)
                return
            comprehension = range_sum(node)
            reversed_value = reversed_list(node)
            if heap and reversed_value is not None:
                for builtin in ('list', 'reversed'):
                    if builtin in scope or bindings(module, builtin):
                        reject(node, f'reversed copies require the unshadowed builtin {builtin}')
                recurse(reversed_value)
                return
            if comprehension is not None and not bindings(module, "sum"):
                for builtin in ('sum', 'range'):
                    if builtin in scope or bindings(module, builtin):
                        reject(node, f'generator sums require the unshadowed builtin {builtin}')
                for argument in comprehension.bounds:
                    recurse(argument)
                inner_scope = scope | {comprehension.name}
                for condition in comprehension.conditions:
                    expr(condition, inner_scope)
                expr(comprehension.element, inner_scope)
                return
            if isinstance(node, ast.Constant) and type(node.value) in (int, str, bytes, bool, type(None)):
                return
            if isinstance(node, ast.Name) and node.id in scope | globals_:
                return
            if heap and isinstance(node, ast.Attribute):
                ordinary_attribute(node, reject)
                recurse(node.value)
                return
            if isinstance(node, ast.JoinedStr):
                if not plain_fstring(node):
                    reject(node, 'f-strings support scalar fields with empty format specifications and optional !s')
                for part in node.values:
                    if isinstance(part, ast.FormattedValue):
                        recurse(part.value)
                return
            if heap and isinstance(node, ast.Dict):
                for key, value in zip(node.keys, node.values):
                    if key is None:
                        reject(node, 'dictionary unpacking is not modeled')
                    else:
                        recurse(key)
                    recurse(value)
                return
            if heap and isinstance(node, ast.Set):
                if len(node.elts) > 30 or any(isinstance(item, ast.Starred) for item in node.elts):
                    reject(node, 'set displays support at most 30 elements without unpacking')
                for item in node.elts:
                    recurse(item)
                return
            if heap and isinstance(node, (ast.List, ast.Tuple)):
                if (isinstance(node, ast.Tuple) and node.elts and node not in hidden_tuples
                        and not any(runtime_tuple_element(item) for item in node.elts)):
                    reject(node, 'nonempty tuple displays need a runtime element; constant-tuple pooling is not modeled')
                for item in node.elts:
                    recurse(item)
                return
            if (heap and isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                    and node.func.attr in ('append', 'add') and len(node.args) == 1 and not node.keywords):
                recurse(node.func.value)
                recurse(node.args[0])
                return
            if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub, ast.Mult, ast.FloorDiv, ast.Mod, ast.Pow, ast.BitAnd, ast.BitOr, ast.BitXor, ast.LShift, ast.RShift)):
                recurse(node.left)
                recurse(node.right)
            elif isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.Not, ast.USub)):
                recurse(node.operand)
            elif heap and isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], (ast.In, ast.NotIn)):
                # An immediately consumed literal never exposes its pooled tuple identity.
                if isinstance(node.comparators[0], ast.Tuple):
                    hidden_tuples.add(node.comparators[0])
                recurse(node.left)
                recurse(node.comparators[0])
            elif identity_comparison(node):
                recurse(node.left)
                recurse(node.comparators[0])
            elif isinstance(node, ast.Compare) and all(isinstance(
                    op, (ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt, ast.GtE)) for op in node.ops):
                recurse(node.left)
                for comparator in node.comparators:
                    recurse(comparator)
            elif isinstance(node, ast.BoolOp):
                for item in node.values:
                    recurse(item)
            elif isinstance(node, ast.IfExp):
                recurse(node.test)
                recurse(node.body)
                recurse(node.orelse)
            elif isinstance(node, ast.Subscript):
                recurse(node.value)
                if isinstance(node.slice, ast.Slice):
                    for bound in (node.slice.lower, node.slice.upper, node.slice.step):
                        if bound is not None:
                            recurse(bound)
                else:
                    recurse(node.slice)
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr in ('bit_length', 'bit_count'):
                if node.args or node.keywords:
                    reject(node, f'int.{node.func.attr} requires no arguments')
                recurse(node.func.value)
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in functions:
                if node.func.id in scope:
                    reject(node, 'local bindings must not shadow module-level call targets')
                target = functions[node.func.id]
                if node.keywords or not len(target.args.args) - len(target.args.defaults) <= len(node.args) <= len(target.args.args):
                    reject(node, 'calls require the declared positional arguments, with trailing defaults optional')
                for item in node.args:
                    recurse(item)
                visit(target)
            elif isinstance(node, ast.Call) and library_name(node.func) in libraries:
                target = library_name(node.func)
                binding = target.split('.')[0]
                if binding in scope or bindings(module, binding) != [libraries[target][2]]:
                    reject(node, 'standard-library call targets must not be rebound or shadowed')
                # A write through any alias changes the shared module, including
                # writes in other functions that may run before this call.
                aliases = {name.split('.')[0] for name in libraries if '.' in name}
                if any(isinstance(part, ast.Attribute) and isinstance(part.ctx, (ast.Store, ast.Del))
                       and isinstance(part.value, ast.Name) and part.value.id in aliases
                       for part in ast.walk(module)):
                    reject(node, 'modeled standard-library modules must not be mutated')
                primitive = libraries[target][1]
                if primitive in ('isqrt', 'factorial') and (node.keywords or len(node.args) != 1):
                    reject(node, f'math.{primitive} requires exactly one positional argument')
                elif primitive == 'comb' and (node.keywords or len(node.args) != 2):
                    reject(node, 'math.comb requires exactly two positional arguments')
                elif node.keywords:
                    reject(node, f'math.{primitive} accepts only positional arguments')
                source = getattr(module, 'formalsw_source', None)
                if source is not None and any((root / 'math.py').exists() or (root / 'math').is_dir()
                                              for root in (source.parent, Path.cwd())):
                    reject(node, 'a local math module shadows the modeled standard library')
                for item in node.args:
                    recurse(item)
            elif heap and isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in classes:
                if node.func.id in scope or node.keywords:
                    reject(node, 'class construction requires an unshadowed name and positional arguments')
                for item in node.args:
                    recurse(item)
                visit_class(classes[node.func.id])
            elif heap and isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
                ordinary_attribute(node.func, reject)
                reverse = reverse_keyword(node)
                if node.keywords and not (node.func.attr == 'sort' and not node.args and reverse is not None):
                    reject(node, 'method keywords support only sort(reverse=...)')
                recurse(node.func.value)
                for item in node.args:
                    recurse(item)
                if reverse is not None:
                    recurse(reverse)
            elif heap and isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in ('list', 'tuple'):
                if node.func.id in scope or bindings(module, node.func.id):
                    reject(node, f'{node.func.id} construction requires the unshadowed builtin {node.func.id}')
                if len(node.args) > 1 or node.keywords:
                    reject(node, f'{node.func.id} supports zero or one positional argument')
                for item in node.args:
                    recurse(item)
            elif heap and isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'sorted':
                if node.func.id in scope or bindings(module, node.func.id):
                    reject(node, 'sorting requires the unshadowed builtin sorted')
                reverse = reverse_keyword(node)
                if len(node.args) != 1 or node.keywords and reverse is None:
                    reject(node, 'sorted supports one positional iterable and optional reverse; key is not modeled')
                for item in node.args:
                    recurse(item)
                if reverse is not None:
                    recurse(reverse)
            elif heap and isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'set':
                if node.func.id in scope or bindings(module, node.func.id):
                    reject(node, 'set construction requires the unshadowed builtin set')
                if len(node.args) > 1 or node.keywords:
                    reject(node, 'set supports zero or one positional argument')
                for item in node.args:
                    recurse(item)
            elif heap and isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'bytearray':
                if node.func.id in scope or bindings(module, node.func.id):
                    reject(node, 'buffer construction requires the unshadowed builtin bytearray')
                if node.keywords or len(node.args) > 1:
                    reject(node, 'bytearray supports zero or one positional argument; encoding arguments are not modeled')
                for item in node.args:
                    recurse(item)
            elif heap and isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'divmod':
                if node.func.id in scope or bindings(module, node.func.id):
                    reject(node, 'divmod requires the unshadowed builtin divmod')
                if node.keywords or len(node.args) != 2:
                    reject(node, 'divmod requires exactly two positional arguments')
                for item in node.args:
                    recurse(item)
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in ('all', 'any'):
                if not heap:
                    reject(node, 'truth consumers require heap call execution')
                if node.func.id in scope or bindings(module, node.func.id):
                    reject(node, f'truth consumption requires the unshadowed builtin {node.func.id}')
                if node.keywords or len(node.args) != 1:
                    reject(node, f'{node.func.id} requires one positional argument')
                for item in node.args:
                    recurse(item)
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'pow':
                if node.func.id in scope or bindings(module, node.func.id):
                    reject(node, 'power requires the unshadowed builtin pow')
                if node.keywords or len(node.args) not in (2, 3):
                    reject(node, 'pow requires two or three positional arguments')
                for item in node.args:
                    recurse(item)
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'abs':
                if node.func.id in scope or bindings(module, node.func.id):
                    reject(node, 'absolute value requires the unshadowed builtin abs')
                if node.keywords or len(node.args) != 1:
                    reject(node, 'abs requires exactly one positional argument')
                for item in node.args:
                    recurse(item)
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'isinstance':
                for builtin in ('isinstance', 'int'):
                    if builtin in scope or bindings(module, builtin):
                        reject(node, f'integer type tests require the unshadowed builtin {builtin}')
                if not integer_instance(node):
                    reject(node, 'isinstance supports exactly two positional arguments with builtin int as classinfo')
                if node.args:
                    recurse(node.args[0])
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'bin':
                if node.func.id in scope or bindings(module, node.func.id):
                    reject(node, 'binary conversion requires the unshadowed builtin bin')
                if node.keywords:
                    reject(node, 'bin keyword arguments are not modeled')
                for item in node.args:
                    recurse(item)
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'ord':
                if node.func.id in scope or bindings(module, node.func.id):
                    reject(node, 'ordinal conversion requires the unshadowed builtin ord')
                if node.keywords or len(node.args) != 1:
                    reject(node, 'ord requires exactly one positional argument')
                for item in node.args:
                    recurse(item)
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'len':
                if node.func.id in scope or bindings(module, node.func.id):
                    reject(node, 'length requires the unshadowed builtin len')
                if node.keywords or len(node.args) != 1:
                    reject(node, 'len requires exactly one positional argument')
                for item in node.args:
                    recurse(item)
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'int':
                if node.func.id in scope or bindings(module, node.func.id):
                    reject(node, 'integer conversion requires the unshadowed builtin int')
                if node.keywords or len(node.args) > 1:
                    reject(node, 'int supports zero or one positional argument; explicit bases are not modeled')
                for item in node.args:
                    recurse(item)
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'bool':
                if node.func.id in scope or bindings(module, node.func.id):
                    reject(node, 'Boolean conversion requires the unshadowed builtin bool')
                if node.keywords or len(node.args) > 1:
                    reject(node, 'bool supports zero or one positional argument')
                for item in node.args:
                    recurse(item)
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'str':
                if node.func.id in scope or bindings(module, node.func.id):
                    reject(node, 'string conversion requires the unshadowed builtin str')
                if node.keywords or len(node.args) > 1:
                    reject(node, 'scalar str supports zero or one positional argument')
                if heap and any(isinstance(item, ast.List) for item in node.args):
                    reject(node, 'list string conversion is not yet supported by heap call execution')
                for item in node.args:
                    recurse(item)
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in ('min', 'max'):
                if node.func.id in scope or bindings(module, node.func.id):
                    reject(node, f'{node.func.id} requires the unshadowed builtin {node.func.id}')
                if node.keywords or len(node.args) < (1 if heap else 2):
                    reject(node, f'{node.func.id} requires positional arguments and no keywords; scalar execution needs at least two')
                for item in node.args:
                    recurse(item)
            else:
                reject(node, f'{type(node).__name__} expression is unsupported by call execution')

        def block(body, loop_depth=0):
            for node in body:
                if isinstance(node, (ast.Break, ast.Continue)):
                    if not loop_depth:
                        reject(node, 'break and continue require an enclosing loop body')
                elif isinstance(node, ast.Pass):
                    pass
                elif isinstance(node, ast.Return):
                    if node.value is not None:
                        expr(node.value)
                elif isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
                    expr(node.value)
                elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
                    # Function-local annotations are never evaluated by Python.
                    if node.value is not None:
                        expr(node.value)
                elif (heap and isinstance(node, ast.Assign) and len(node.targets) == 1
                      and isinstance(node.targets[0], ast.Attribute)):
                    expr(node.value)
                    ordinary_attribute(node.targets[0], reject)
                    expr(node.targets[0].value)
                elif heap and isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Attribute):
                    if node.value is not None:
                        expr(node.value)
                    ordinary_attribute(node.target, reject)
                    expr(node.target.value)
                elif (heap and isinstance(node, ast.Assign) and len(node.targets) == 1
                      and isinstance(node.targets[0], (ast.Tuple, ast.List))
                      and all(isinstance(target, ast.Name) for target in node.targets[0].elts)):
                    if isinstance(node.value, ast.Tuple):
                        # The container cannot escape immediate unpacking; its
                        # children still need ordinary expression coverage.
                        for value in node.value.elts:
                            expr(value)
                    else:
                        expr(node.value)
                elif (isinstance(node, ast.Assign) and len(node.targets) == 1
                      and isinstance(node.targets[0], ast.Tuple) and isinstance(node.value, ast.Tuple)
                      and all(isinstance(target, ast.Name) for target in node.targets[0].elts)
                      and len(node.targets[0].elts) == len(node.value.elts)):
                    for value in node.value.elts:
                        expr(value)
                elif heap and isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Subscript):
                    expr(node.value)
                    expr(node.targets[0])
                elif (heap and isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Subscript)
                      and not isinstance(node.target.slice, ast.Slice)):
                    expr(ast.BinOp(node.target, node.op, node.value))
                elif isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name):
                    expr(ast.BinOp(node.target, node.op, node.value))
                elif heap and isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Attribute):
                    expr(ast.BinOp(node.target, node.op, node.value))
                elif isinstance(node, ast.Assert):
                    expr(node.test)
                    if node.msg is not None:
                        expr(node.msg)
                elif isinstance(node, ast.Raise):
                    target = node.exc.func if isinstance(node.exc, ast.Call) else node.exc
                    if (node.cause is not None or not isinstance(target, ast.Name)
                            or target.id not in PLAIN_EXCEPTIONS
                            or target.id in locals_ or bindings(module, target.id)):
                        reject(node, 'raise requires an unshadowed supported builtin exception constructor')
                    if isinstance(node.exc, ast.Call):
                        if node.exc.keywords:
                            reject(node, 'exception constructors require positional arguments')
                        for argument in node.exc.args:
                            expr(argument)
                elif isinstance(node, (ast.If, ast.While)):
                    expr(node.test)
                    block(node.body, loop_depth + isinstance(node, ast.While))
                    block(node.orelse, loop_depth)
                elif (isinstance(node, ast.For) and isinstance(node.target, ast.Name)
                      and isinstance(node.iter, ast.Call) and isinstance(node.iter.func, ast.Name)
                      and node.iter.func.id == 'range' and 1 <= len(node.iter.args) <= 3
                      and not node.iter.keywords):
                    if 'range' in locals_ or bindings(module, 'range'):
                        reject(node, 'range loops require the unshadowed builtin range')
                    for argument in node.iter.args:
                        expr(argument)
                    block(node.body, loop_depth + 1)
                    block(node.orelse, loop_depth)
                elif (heap and isinstance(node, ast.For) and isinstance(node.iter, ast.Call)
                      and isinstance(node.iter.func, ast.Name) and node.iter.func.id == 'enumerate'):
                    if 'enumerate' in locals_ or bindings(module, 'enumerate'):
                        reject(node, 'enumerate loops require the unshadowed builtin enumerate')
                    if (not isinstance(node.target, (ast.Tuple, ast.List)) or len(node.target.elts) != 2
                            or not all(isinstance(target, ast.Name) for target in node.target.elts)):
                        reject(node, 'enumerate loops require immediate unpacking into two local names')
                    arguments = enumerate_arguments(node.iter)
                    if arguments is None:
                        reject(node, 'enumerate loops support an iterable and optional positional or keyword start')
                    else:
                        for argument in arguments:
                            expr(argument)
                    block(node.body, loop_depth + 1)
                    block(node.orelse, loop_depth)
                elif heap and isinstance(node, ast.For) and reversed_sequence(node.iter, module):
                    if 'reversed' in locals_:
                        reject(node.iter, 'reverse iteration requires the unshadowed builtin reversed')
                    if not isinstance(node.target, ast.Name):
                        reject(node, 'reverse loops currently require a local name target')
                    if len(node.iter.args) != 1 or node.iter.keywords:
                        reject(node.iter, 'reversed requires one positional sequence argument')
                    for argument in node.iter.args:
                        if isinstance(argument, ast.Tuple):
                            hidden_tuples.add(argument)
                        expr(argument)
                    block(node.body, loop_depth + 1)
                    block(node.orelse, loop_depth)
                elif heap and isinstance(node, ast.For) and permutation_binding(node.iter, module) is not None:
                    if permutation_binding(node.iter, module) in locals_:
                        reject(node.iter, 'permutations requires an unshadowed standard-library import')
                    if not (isinstance(node.target, ast.Name) or flat_unpacking(node.target)):
                        reject(node, 'permutation loops require a name or flat tuple/list target')
                    arguments = permutation_arguments(node.iter, module)
                    if arguments is None:
                        reject(node.iter, 'permutations requires a positional iterable and optional length')
                    else:
                        for argument in arguments:
                            if isinstance(argument, ast.Tuple):
                                hidden_tuples.add(argument)
                            expr(argument)
                    block(node.body, loop_depth + 1)
                    block(node.orelse, loop_depth)
                elif heap and isinstance(node, ast.For) and zip_iterable(node.iter, module):
                    if 'zip' in locals_:
                        reject(node.iter, 'zip iteration requires the unshadowed builtin zip')
                    if not (isinstance(node.target, ast.Name) or flat_unpacking(node.target)):
                        reject(node, 'zip loops require a name or flat tuple/list target')
                    if node.iter.keywords:
                        reject(node.iter, 'zip iteration supports positional sequence arguments, without strict')
                    for argument in node.iter.args:
                        if isinstance(argument, ast.Tuple):
                            hidden_tuples.add(argument)
                        expr(argument)
                    block(node.body, loop_depth + 1)
                    block(node.orelse, loop_depth)
                elif heap and isinstance(node, ast.For) and isinstance(node.target, ast.Name):
                    expr(node.iter)
                    block(node.body, loop_depth + 1)
                    block(node.orelse, loop_depth)
                elif heap and isinstance(node, ast.For) and flat_unpacking(node.target):
                    expr(node.iter)
                    block(node.body, loop_depth + 1)
                    block(node.orelse, loop_depth)
                elif isinstance(node, ast.Expr):
                    expr(node.value)
                else:
                    reject(node, f'{type(node).__name__} statement is unsupported by call execution')
        block(function.body)

    visit(function)
