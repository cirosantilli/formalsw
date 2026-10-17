"""Coverage checks for scalar functions with ordinary recursive calls."""
import ast
from pathlib import Path
from lang.py.global_inputs import GlobalInputError, function_globals, annotation_kind
from lang.py.imports import bindings
from lang.py.defaults import literal_default


def range_sum(node):
    """Recognize sum(element for name in range(...) if ...), without executing it."""
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'sum' and len(node.args) == 1 and not node.keywords
            and isinstance(node.args[0], ast.GeneratorExp)):
        return None
    generator = node.args[0]
    if len(generator.generators) != 1:
        return None
    loop = generator.generators[0]
    if not (isinstance(loop.target, ast.Name) and not loop.is_async
            and isinstance(loop.iter, ast.Call) and isinstance(loop.iter.func, ast.Name)
            and loop.iter.func.id == 'range' and 1 <= len(loop.iter.args) <= 3
            and not loop.iter.keywords):
        return None
    return generator, loop


def library_functions(module):
    """Supported standard-library functions, preserving their import bindings."""
    return {alias.asname or alias.name: (node.module, alias.name, node)
            for node in module.body if isinstance(node, ast.ImportFrom)
            and node.level == 0 and node.module == 'math'
            for alias in node.names if alias.name == 'isqrt'}


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
    functions = {node.name: node for node in module.body if isinstance(node, ast.FunctionDef)}
    pending = [function]
    visited = set()
    while pending:
        current = pending.pop()
        if current.name in visited:
            continue
        visited.add(current.name)
        for node in ast.walk(current):
            if isinstance(node, (ast.BinOp, ast.AugAssign)) and isinstance(node.op, ast.Pow):
                return True
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in functions:
                pending.append(functions[node.func.id])
    return False


def uses_heap_calls(module, function):
    """Find list allocation or use in the transitive local call graph."""
    functions = {node.name: node for node in module.body if isinstance(node, ast.FunctionDef)}
    pending, visited = [function], set()
    while pending:
        current = pending.pop()
        if current.name in visited:
            continue
        visited.add(current.name)
        kinds = [annotation_kind(arg.annotation) for arg in current.args.args]
        kinds.append(annotation_kind(current.returns))
        if any(kind and kind.startswith('list[') for kind in kinds):
            return True
        # Defaults are evaluated at definition time, outside the modeled body.
        # Their validation must not select a different execution backend.
        for node in (part for statement in current.body for part in ast.walk(statement)):
            if isinstance(node, ast.List) or (isinstance(node, ast.Attribute) and node.attr == 'append'):
                return True
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in functions:
                pending.append(functions[node.func.id])
    return False


def uses_calls_model(module, function):
    if not all(isinstance(arg.annotation, ast.Name) and arg.annotation.id in ('int', 'str', 'bool')
               for arg in function.args.args):
        return False
    try:
        if function_globals(module, function):
            return False
    except GlobalInputError:
        return False
    names = {node.name for node in module.body if isinstance(node, ast.FunctionDef)}
    names.update(library_functions(module))
    return bool(function.args.defaults) or uses_heap_calls(module, function) or any(
        isinstance(node, (ast.IfExp, ast.GeneratorExp, ast.Break, ast.Continue, ast.Subscript))
        or general_division(node)
        or isinstance(node, (ast.BinOp, ast.AugAssign)) and isinstance(node.op, ast.Pow)
        or isinstance(node, ast.Assign) and any(isinstance(target, ast.Tuple) for target in node.targets)
        or isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in names | {'str'}
        or isinstance(node, ast.For) and isinstance(node.iter, ast.Call)
        and isinstance(node.iter.func, ast.Name) and node.iter.func.id == 'range' and len(node.iter.args) != 1
        for node in ast.walk(function)
    )


def check_calls(module, function, reject, *, heap=False):
    functions = {node.name: node for node in module.body if isinstance(node, ast.FunctionDef)}
    libraries = library_functions(module)
    visited = set()

    def visit(function):
        if function.name in visited:
            return
        visited.add(function.name)
        if sum(isinstance(node, ast.FunctionDef) and node.name == function.name
               for node in module.body) != 1:
            reject(function, 'call targets must have one module-level definition')
        for node in module.body:
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
        if function.decorator_list or function.args.posonlyargs or \
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
        if locals_ & functions.keys():
            reject(function, 'local bindings must not shadow module-level call targets')
        for arg in function.args.args:
            kind = annotation_kind(arg.annotation)
            if kind not in ('int', 'str', 'bool') and not (heap and kind and kind.startswith('list[')):
                reject(arg, 'call arguments require scalar annotations or supported heap list annotations' if heap
                       else 'call arguments require scalar int, str, or bool annotations')

        def expr(node, scope=None):
            scope = locals_ if scope is None else scope
            recurse = lambda child: expr(child, scope)
            comprehension = range_sum(node)
            if comprehension is not None:
                if heap:
                    reject(node, "generator sums are not yet supported by heap call execution")
                generator, loop = comprehension
                for builtin in ('sum', 'range'):
                    if builtin in scope or bindings(module, builtin):
                        reject(node, f'generator sums require the unshadowed builtin {builtin}')
                for argument in loop.iter.args:
                    recurse(argument)
                inner_scope = scope | {loop.target.id}
                for condition in loop.ifs:
                    expr(condition, inner_scope)
                expr(generator.elt, inner_scope)
                return
            if isinstance(node, ast.Constant) and type(node.value) in (int, str, bool, type(None)):
                return
            if isinstance(node, ast.Name) and node.id in scope:
                return
            if heap and isinstance(node, ast.List):
                for item in node.elts:
                    recurse(item)
                return
            if (heap and isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                    and node.func.attr == 'append' and len(node.args) == 1 and not node.keywords):
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
                if heap and len(node.ops) != 1:
                    reject(node, "chained comparisons are not yet supported by heap call execution")
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
                    if heap:
                        reject(node, "slices are not yet supported by heap call execution")
                    for bound in (node.slice.lower, node.slice.upper, node.slice.step):
                        if bound is not None:
                            recurse(bound)
                else:
                    recurse(node.slice)
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in functions:
                if node.func.id in scope:
                    reject(node, 'local bindings must not shadow module-level call targets')
                target = functions[node.func.id]
                if node.keywords or not len(target.args.args) - len(target.args.defaults) <= len(node.args) <= len(target.args.args):
                    reject(node, 'calls require the declared positional arguments, with trailing defaults optional')
                for item in node.args:
                    recurse(item)
                visit(target)
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in libraries:
                target = node.func.id
                if heap:
                    reject(node, "standard-library calls are not yet supported by heap call execution")
                if target in scope or bindings(module, target) != [libraries[target][2]]:
                    reject(node, 'standard-library call targets must not be rebound or shadowed')
                if node.keywords or len(node.args) != 1:
                    reject(node, 'math.isqrt requires exactly one positional argument')
                source = getattr(module, 'formalsw_source', None)
                if source is not None and any((root / 'math.py').exists() or (root / 'math').is_dir()
                                              for root in (source.parent, Path.cwd())):
                    reject(node, 'a local math module shadows the modeled standard library')
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
                elif (isinstance(node, ast.Assign) and len(node.targets) == 1
                      and isinstance(node.targets[0], ast.Tuple) and isinstance(node.value, ast.Tuple)
                      and all(isinstance(target, ast.Name) for target in node.targets[0].elts)
                      and len(node.targets[0].elts) == len(node.value.elts)):
                    if heap:
                        reject(node, "tuple unpacking is not yet supported by heap call execution")
                    for value in node.value.elts:
                        expr(value)
                elif isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name):
                    expr(ast.BinOp(node.target, node.op, node.value))
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
                elif isinstance(node, ast.Expr):
                    expr(node.value)
                else:
                    reject(node, f'{type(node).__name__} statement is unsupported by call execution')
        block(function.body)

    visit(function)
