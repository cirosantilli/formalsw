"""Coverage checks for scalar functions with ordinary recursive calls."""
import ast
from lang.py.global_inputs import GlobalInputError, function_globals
from lang.py.imports import bindings


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
    return any(
        isinstance(node, ast.IfExp)
        or isinstance(node, ast.Assign) and any(isinstance(target, ast.Tuple) for target in node.targets)
        or isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in names
        or isinstance(node, ast.For) and isinstance(node.iter, ast.Call)
        and isinstance(node.iter.func, ast.Name) and node.iter.func.id == 'range' and len(node.iter.args) != 1
        for node in ast.walk(function)
    )


def check_calls(module, function, reject):
    functions = {node.name: node for node in module.body if isinstance(node, ast.FunctionDef)}
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
        locals_.update(node.id for node in ast.walk(function)
                       if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store))
        if locals_ & functions.keys():
            reject(function, 'local bindings must not shadow module-level call targets')
        for arg in function.args.args:
            if not isinstance(arg.annotation, ast.Name) or arg.annotation.id not in ('int', 'str', 'bool'):
                reject(arg, 'call arguments require scalar int, str, or bool annotations')

        def expr(node):
            if isinstance(node, ast.Constant) and type(node.value) in (int, str, bool, type(None)):
                return
            if isinstance(node, ast.Name) and node.id in locals_:
                return
            if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub, ast.Mult, ast.FloorDiv, ast.Mod)):
                expr(node.left)
                expr(node.right)
            elif isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.Not, ast.USub)):
                expr(node.operand)
            elif isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(
                    node.ops[0], (ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt, ast.GtE)):
                expr(node.left)
                expr(node.comparators[0])
            elif isinstance(node, ast.BoolOp):
                for item in node.values:
                    expr(item)
            elif isinstance(node, ast.IfExp):
                expr(node.test)
                expr(node.body)
                expr(node.orelse)
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in functions:
                target = functions[node.func.id]
                if node.keywords or len(node.args) != len(target.args.args):
                    reject(node, 'calls require exactly the declared positional arguments')
                for item in node.args:
                    expr(item)
                visit(target)
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
