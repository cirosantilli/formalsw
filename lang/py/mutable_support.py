"""Whole-body validation for the heap interpreter (no function-shape matching).

Entry lists have scalar element domains. Writes can change element types, so
reads conservatively yield any scalar; aliases never invalidate this analysis.
Nested mutable containers and recursive list comparisons are rejected explicitly.
"""
import ast
import builtins
from lang.py.global_inputs import annotation_kind

SCALARS = frozenset(('int', 'str', 'bool', 'none'))


def check_mutable(function, globals, bindings, reject):
    env = {item.name: frozenset(('list' if item.kind.startswith('list[') else item.kind,)) for item in globals}
    for arg in function.args.args:
        kind = annotation_kind(arg.annotation)
        if kind is None:
            reject(arg, 'heap arguments need int, str, bool, or list[int/str/bool] annotations')
        else:
            env[arg.arg] = frozenset(('list' if kind.startswith('list[') else kind,))
    # Python scope is determined by the whole body, not statement order.
    declared = {name for node in ast.walk(function) if isinstance(node, ast.Global) for name in node.names}
    for node in ast.walk(function):
        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store) and node.id not in declared:
            if node.id not in {arg.arg for arg in function.args.args}:
                env.pop(node.id, None)
    shadowed = bindings | {node.id for node in ast.walk(function) if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store)} | {arg.arg for arg in function.args.args}

    def expression(node, env):
        if node is None:
            return frozenset(('none',))
        if isinstance(node, ast.Constant):
            kind = {int: 'int', str: 'str', bool: 'bool', type(None): 'none'}.get(type(node.value))
            if kind:
                return frozenset((kind,))
        elif isinstance(node, ast.Name):
            if node.id not in env:
                reject(node, f'unbound or possibly unbound variable {node.id!r} is unsupported')
            return env.get(node.id, frozenset())
        elif isinstance(node, ast.List):
            for item in node.elts:
                if not expression(item, env) <= SCALARS:
                    reject(item, 'nested mutable containers are not yet supported by heap source validation')
            return frozenset(('list',))
        elif isinstance(node, ast.Subscript):
            base = expression(node.value, env)
            index = expression(node.slice, env)
            if not base <= {'list'} or not index <= SCALARS:
                reject(node, 'heap subscripts currently require a list and scalar index')
            return SCALARS
        elif isinstance(node, ast.BinOp):
            left, right = expression(node.left, env), expression(node.right, env)
            if not isinstance(node.op, (ast.Add, ast.Sub, ast.Mult, ast.FloorDiv, ast.Mod)):
                reject(node, 'unsupported heap binary operator')
            if isinstance(node.op, (ast.FloorDiv, ast.Mod)) and not (
                    isinstance(node.right, ast.Constant) and type(node.right.value) is int and node.right.value >= 0):
                reject(node, 'division and modulo currently require a nonnegative integer literal divisor')
            kinds = {'int'} if left & {'int', 'bool'} and right & {'int', 'bool'} else set()
            if isinstance(node.op, ast.Add):
                if 'list' in left and 'list' in right:
                    kinds.add('list')
                if 'str' in left and 'str' in right:
                    kinds.add('str')
            if isinstance(node.op, ast.Mult):
                for kind in ('str', 'list'):
                    if kind in left and right & {'int', 'bool'} or kind in right and left & {'int', 'bool'}:
                        kinds.add(kind)
            return frozenset(kinds)
        elif isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.Not, ast.USub)):
            expression(node.operand, env)
            return frozenset(('bool' if isinstance(node.op, ast.Not) else 'int',))
        elif isinstance(node, ast.Compare):
            kinds = expression(node.left, env)
            for right in node.comparators:
                kinds |= expression(right, env)
            if len(node.ops) != 1 or not isinstance(node.ops[0], (ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt, ast.GtE)):
                reject(node, 'heap comparisons require one supported comparison operator')
            if not kinds <= SCALARS:
                reject(node, 'recursive list comparison is not yet supported by heap execution')
            return frozenset(('bool',))
        elif isinstance(node, ast.Call) and not node.keywords:
            if isinstance(node.func, ast.Name) and node.func.id == 'len' and len(node.args) == 1 and 'len' not in shadowed:
                expression(node.args[0], env)
                return frozenset(('int',))
            if isinstance(node.func, ast.Attribute) and node.func.attr == 'append' and len(node.args) == 1:
                if not expression(node.func.value, env) <= {'list'}:
                    reject(node, 'append requires a list receiver')
                if not expression(node.args[0], env) <= SCALARS:
                    reject(node, 'nested mutable containers are not yet supported by heap source validation')
                return frozenset(('none',))
        reject(node, f'{type(node).__name__} expression is unsupported by heap execution')
        return frozenset()

    def target(node, kind, env):
        if isinstance(node, ast.Name):
            env[node.id] = kind
        elif isinstance(node, ast.Subscript):
            expression(node, env)
            if not kind <= SCALARS:
                reject(node, 'nested mutable containers are not yet supported by heap source validation')
        else:
            reject(node, 'heap assignment requires a name or list index')

    def join(a, b):
        return {name: a[name] | b[name] for name in a.keys() & b.keys()}

    def block(body, env):
        env = env.copy()
        for stmt in body:
            if isinstance(stmt, (ast.Pass, ast.Global)):
                continue
            if isinstance(stmt, (ast.Return, ast.Expr)):
                expression(stmt.value, env)
            elif isinstance(stmt, ast.Assign) and len(stmt.targets) == 1:
                target(stmt.targets[0], expression(stmt.value, env), env)
            elif isinstance(stmt, ast.AugAssign):
                expr = ast.copy_location(ast.BinOp(left=stmt.target, op=stmt.op, right=stmt.value), stmt)
                result = expression(expr, env)
                if isinstance(stmt.op, ast.Add) and 'list' in expression(stmt.target, env):
                    if 'str' in expression(stmt.value, env):
                        result |= frozenset(('list',))
                target(stmt.target, result, env)
            elif isinstance(stmt, ast.If):
                expression(stmt.test, env)
                env = join(block(stmt.body, env), block(stmt.orelse, env))
            elif isinstance(stmt, ast.While):
                before = env.copy()
                while True:
                    expression(stmt.test, env)
                    after = join(before, join(env, block(stmt.body, env)))
                    if after == env:
                        break
                    env = after
                env = block(stmt.orelse, env)
            elif isinstance(stmt, ast.Assert) and stmt.msg is None:
                expression(stmt.test, env)
            elif isinstance(stmt, ast.Raise) and stmt.exc is not None and stmt.cause is None:
                call = stmt.exc
                name = call.func if isinstance(call, ast.Call) else call
                cls = getattr(builtins, name.id, None) if isinstance(name, ast.Name) else None
                if not isinstance(cls, type) or not issubclass(cls, BaseException) or name.id in shadowed:
                    reject(stmt, 'only builtin exception constructors are supported in raise')
                elif cls.__init__ is not BaseException.__init__ or issubclass(cls, getattr(builtins, 'BaseExceptionGroup', ())):
                    reject(stmt, 'special builtin exception constructors are unsupported by heap execution')
                if isinstance(call, ast.Call):
                    if call.keywords:
                        reject(call, 'keyword exception arguments are unsupported')
                    for arg in call.args:
                        if not expression(arg, env) <= SCALARS:
                            reject(arg, 'exception arguments must be scalars')
            else:
                reject(stmt, f'{type(stmt).__name__} statement is unsupported by heap execution')
        return env

    body = function.body
    if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) and isinstance(body[0].value.value, str):
        body = body[1:]
    block(body, env)
