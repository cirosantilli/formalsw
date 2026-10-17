"""Coverage checks for scalar functions with ordinary recursive calls."""
import ast
import re
from dataclasses import dataclass
from pathlib import Path
from lang.py.global_inputs import GlobalInputError, function_globals, annotation_kind
from lang.py.imports import bindings
from lang.py.defaults import literal_default
from lang.py.sorting_support import uses_sort_model
from lang.py.tuple_support import flat_unpacking, unpacked_tuple_displays
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
            for alias in node.names if alias.name in ('isqrt', 'gcd')}
    for node in module.body:
        if isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name == 'math':
                    for name in ('isqrt', 'gcd'):
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
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                if node.func.id == name:
                    return True
                if node.func.id in functions:
                    pending.append(functions[node.func.id])
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
                if isinstance(node.func, ast.Name) and node.func.id in functions:
                    pending.append(functions[node.func.id])
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
                if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in functions:
                    pending.append(functions[node.func.id])
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


def has_partial_primitives(module, function):
    """Follow local callees to operations that need a runtime coverage proof."""
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
            if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                    and node.func.id == 'int' and not bindings(module, 'int')):
                return True
            if isinstance(node, (ast.BinOp, ast.AugAssign)) and isinstance(node.op, ast.Pow):
                return True
            if byte_values and isinstance(node, (ast.BinOp, ast.AugAssign)) and isinstance(node.op, ast.Mod):
                return True
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in functions:
                pending.append(functions[node.func.id])
    return False


def uses_heap_calls(module, function):
    """Find list allocation or use in the transitive local call graph."""
    functions = {node.name: node for node in module.body if isinstance(node, ast.FunctionDef)}
    classes = {node.name for node in module.body if isinstance(node, ast.ClassDef)}
    pending, visited = [function], set()
    while pending:
        current = pending.pop()
        if current.name in visited:
            continue
        visited.add(current.name)
        kinds = [annotation_kind(arg.annotation) for arg in current.args.args]
        kinds.append(annotation_kind(current.returns))
        if any(kind and (kind.startswith(('list[', 'set[')) or kind == 'bytearray') for kind in kinds):
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
            if (isinstance(node, (ast.List, ast.ListComp)) or reversed_list(node) is not None
                    or sequence_sum(node) is not None and not bindings(module, "sum")
                    or isinstance(node, ast.Tuple) and isinstance(node.ctx, ast.Load) and id(node) not in scalar_displays
                    or isinstance(node, ast.For) and not (isinstance(node.iter, ast.Call)
                        and isinstance(node.iter.func, ast.Name) and node.iter.func.id == 'range')
                    or isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in classes | {"bytearray", "set", "sorted"}
                    or isinstance(node, ast.Attribute) and node.attr in ('append', 'add')):
                return True
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in functions:
                pending.append(functions[node.func.id])
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
    try:
        if function_globals(module, function):
            return False
    except GlobalInputError:
        return False
    names = {node.name for node in module.body if isinstance(node, ast.FunctionDef)}
    names.update(library_functions(module))
    if (any(annotation_kind(arg.annotation) == 'bytes' for arg in function.args.args)
            or function.args.defaults or uses_heap_calls(module, function)
            or uses_method(module, function, "bit_length")):
        return True
    return any(
        isinstance(node, (ast.IfExp, ast.GeneratorExp, ast.Break, ast.Continue, ast.Subscript, ast.Assert, ast.JoinedStr, ast.AnnAssign))
        or isinstance(node, ast.Constant) and type(node.value) is bytes
        or range_sum(node) is not None
        or general_division(node)
        or isinstance(node, (ast.BinOp, ast.AugAssign)) and isinstance(node.op, ast.Pow)
        or isinstance(node, ast.Assign) and any(isinstance(target, ast.Tuple) for target in node.targets)
        or isinstance(node, ast.Call) and library_name(node.func) in names | {'int', 'str', 'max', 'len'}
        or isinstance(node, ast.For) and isinstance(node.iter, ast.Call)
        and isinstance(node.iter.func, ast.Name) and node.iter.func.id == 'range' and len(node.iter.args) != 1
        for node in ast.walk(function)
    )


def check_calls(module, function, reject, *, heap=False):
    functions = {node.name: node for node in module.body if isinstance(node, ast.FunctionDef)}
    classes = {node.name: node for node in module.body if isinstance(node, ast.ClassDef)}
    libraries = library_functions(module)
    visited = set()
    visited_classes = set()

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
        if function.decorator_list or getattr(function, 'type_params', []) or function.args.posonlyargs or \
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
        hidden_tuples = unpacked_tuple_displays(function) if heap else set()
        if locals_ & (functions.keys() | classes.keys()):
            reject(function, 'local bindings must not shadow module-level call targets')
        for index, arg in enumerate(function.args.args):
            if owner is not None and index == 0:
                continue
            if heap and isinstance(arg.annotation, ast.Name) and arg.annotation.id in classes:
                visit_class(classes[arg.annotation.id])
                continue
            kind = annotation_kind(arg.annotation)
            if kind not in ('int', 'str', 'bytes', 'bool') and not (heap and kind and (kind.startswith(('list[', 'set[')) or kind in ('bytes', 'bytearray'))):
                reject(arg, 'call arguments require scalar annotations or supported heap list annotations' if heap
                       else 'call arguments require scalar int, str, or bool annotations')

        def expr(node, scope=None):
            scope = locals_ if scope is None else scope
            recurse = lambda child: expr(child, scope)
            if heap and isinstance(node, ast.ListComp):
                if any(generator.is_async or not isinstance(generator.target, ast.Name)
                       for generator in node.generators):
                    reject(node, 'comprehensions require synchronous loops with local name targets')
                    return
                inner_scope = scope | {generator.target.id for generator in node.generators}
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
                    else:
                        expr(iterable, iterable_scope)
                    for condition in generator.ifs:
                        expr(condition, inner_scope)
                expr(node.elt, inner_scope)
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
            if isinstance(node, ast.Name) and node.id in scope:
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
            if heap and isinstance(node, (ast.List, ast.Tuple)):
                if (isinstance(node, ast.Tuple) and node.elts and node not in hidden_tuples
                        and not any(isinstance(item, (ast.Name, ast.Call, ast.Subscript, ast.List, ast.Attribute))
                                    for item in node.elts)):
                    reject(node, 'nonempty tuple displays need a runtime element; constant-tuple pooling is not modeled')
                for item in node.elts:
                    recurse(item)
                return
            if (heap and isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                    and node.func.attr in ('append', 'add') and len(node.args) == 1 and not node.keywords):
                recurse(node.func.value)
                recurse(node.args[0])
                return
            if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub, ast.Mult, ast.FloorDiv, ast.Mod, ast.Pow)):
                recurse(node.left)
                recurse(node.right)
            elif isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.Not, ast.USub)):
                recurse(node.operand)
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
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == 'bit_length':
                if node.args or node.keywords:
                    reject(node, 'int.bit_length requires no arguments')
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
                if primitive == 'isqrt' and (node.keywords or len(node.args) != 1):
                    reject(node, 'math.isqrt requires exactly one positional argument')
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
                if node.keywords:
                    reject(node, 'method calls require positional arguments')
                recurse(node.func.value)
                for item in node.args:
                    recurse(item)
            elif heap and isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'sorted':
                if node.func.id in scope or bindings(module, node.func.id):
                    reject(node, 'sorting requires the unshadowed builtin sorted')
                if len(node.args) != 1 or node.keywords:
                    reject(node, 'sorted supports one positional iterable; key and reverse are not modeled')
                for item in node.args:
                    recurse(item)
            elif heap and isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'set':
                if node.func.id in scope or bindings(module, node.func.id):
                    reject(node, 'set construction requires the unshadowed builtin set')
                if node.args or node.keywords:
                    reject(node, 'set construction currently supports only the empty constructor')
            elif heap and isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'bytearray':
                if node.func.id in scope or bindings(module, node.func.id):
                    reject(node, 'buffer construction requires the unshadowed builtin bytearray')
                if node.keywords or len(node.args) > 1:
                    reject(node, 'bytearray supports zero or one positional argument; encoding arguments are not modeled')
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
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'str':
                if node.func.id in scope or bindings(module, node.func.id):
                    reject(node, 'string conversion requires the unshadowed builtin str')
                if node.keywords or len(node.args) > 1:
                    reject(node, 'scalar str supports zero or one positional argument')
                if heap and any(isinstance(item, ast.List) for item in node.args):
                    reject(node, 'list string conversion is not yet supported by heap call execution')
                for item in node.args:
                    recurse(item)
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'max':
                if node.func.id in scope or bindings(module, node.func.id):
                    reject(node, 'maximum requires the unshadowed builtin max')
                if node.keywords or len(node.args) < (1 if heap else 2):
                    reject(node, 'max requires positional arguments and no keywords; scalar execution needs at least two')
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
                    if not 1 <= len(node.iter.args) <= 2 or node.iter.keywords:
                        reject(node, 'enumerate loops support an iterable and optional positional start')
                    for argument in node.iter.args:
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
