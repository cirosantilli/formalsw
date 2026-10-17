"""Coverage checks for scalar functions with ordinary recursive calls."""
import ast
from pathlib import Path
from lang.py.global_inputs import GlobalInputError, function_globals
from lang.py.imports import bindings


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
    return any(
        isinstance(node, (ast.IfExp, ast.GeneratorExp))
        or general_division(node)
        or isinstance(node, ast.Assign) and any(isinstance(target, ast.Tuple) for target in node.targets)
        or isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in names
        or isinstance(node, ast.For) and isinstance(node.iter, ast.Call)
        and isinstance(node.iter.func, ast.Name) and node.iter.func.id == 'range' and len(node.iter.args) != 1
        for node in ast.walk(function)
    )


def check_calls(module, function, reject):
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
                        or isinstance(item, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef))
                        and item.name == function.name
                        or isinstance(item, (ast.Import, ast.ImportFrom)) and any(
                            (alias.asname or alias.name.split('.')[0]) in (function.name, '*')
                            for alias in item.names)):
                    reject(item, 'module-level call targets must not be rebound')
        if function.decorator_list or function.args.defaults or function.args.posonlyargs or \
                function.args.kwonlyargs or function.args.vararg or function.args.kwarg:
            reject(function, 'call execution requires undecorated plain positional functions')
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
            if not isinstance(arg.annotation, ast.Name) or arg.annotation.id not in ('int', 'str', 'bool'):
                reject(arg, 'call arguments require scalar int, str, or bool annotations')

        def expr(node, scope=None):
            scope = locals_ if scope is None else scope
            recurse = lambda child: expr(child, scope)
            comprehension = range_sum(node)
            if comprehension is not None:
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
            if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub, ast.Mult, ast.FloorDiv, ast.Mod)):
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
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in functions:
                if node.func.id in scope:
                    reject(node, 'local bindings must not shadow module-level call targets')
                target = functions[node.func.id]
                if node.keywords or len(node.args) != len(target.args.args):
                    reject(node, 'calls require exactly the declared positional arguments')
                for item in node.args:
                    recurse(item)
                visit(target)
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in libraries:
                target = node.func.id
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
            else:
                reject(node, f'{type(node).__name__} expression is unsupported by call execution')

        def block(body):
            for node in body:
                if isinstance(node, ast.Return):
                    if node.value is not None:
                        expr(node.value)
                elif isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
                    expr(node.value)
                elif (isinstance(node, ast.Assign) and len(node.targets) == 1
                      and isinstance(node.targets[0], ast.Tuple) and isinstance(node.value, ast.Tuple)
                      and all(isinstance(target, ast.Name) for target in node.targets[0].elts)
                      and len(node.targets[0].elts) == len(node.value.elts)):
                    for value in node.value.elts:
                        expr(value)
                elif isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name):
                    expr(ast.BinOp(node.target, node.op, node.value))
                elif isinstance(node, (ast.If, ast.While)):
                    expr(node.test)
                    block(node.body)
                    block(node.orelse)
                elif (isinstance(node, ast.For) and isinstance(node.target, ast.Name)
                      and isinstance(node.iter, ast.Call) and isinstance(node.iter.func, ast.Name)
                      and node.iter.func.id == 'range' and 1 <= len(node.iter.args) <= 3
                      and not node.iter.keywords):
                    if 'range' in locals_ or bindings(module, 'range'):
                        reject(node, 'range loops require the unshadowed builtin range')
                    for argument in node.iter.args:
                        expr(argument)
                    block(node.body)
                    block(node.orelse)
                elif isinstance(node, ast.Expr):
                    expr(node.value)
                else:
                    reject(node, f'{type(node).__name__} statement is unsupported by call execution')
        block(function.body)

    visit(function)
