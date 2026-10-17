"""Conservative source coverage checks for CleanXY's supported Python models.

A requirement is rejected if any part of its function or a modeled dependency
falls outside the selected model. Both branches and unreachable statements are
checked; sampling inputs or executing the Python program is never used.
"""
from __future__ import annotations

import ast
import builtins
import re
from dataclasses import dataclass


@dataclass(frozen=True)
class UnsupportedConstruct:
    function: str
    line: int
    reason: str
    dependency: tuple[str, ...] = ()


MERGE_SORT = '''
def FUNCTION(ARG):
    if len(ARG) <= 1:
        return ARG
    middle = len(ARG) // 2
    left = FUNCTION(ARG[:middle])
    right = FUNCTION(ARG[middle:])
    merged = []
    left_index = 0
    right_index = 0
    while left_index < len(left) and right_index < len(right):
        if left[left_index] <= right[right_index]:
            merged += [left[left_index]]
            left_index += 1
        else:
            merged += [right[right_index]]
            right_index += 1
    return merged + left[left_index:] + right[right_index:]
'''
QUICK_SORT = '''
def FUNCTION(ARG):
    if len(ARG) <= 1:
        return ARG
    pivot = ARG[0]
    less = []
    equal = []
    greater = []
    for value in ARG:
        if value < pivot:
            less += [value]
        else:
            if value > pivot:
                greater += [value]
            else:
                equal += [value]
    return FUNCTION(less) + equal + FUNCTION(greater)
'''


def body_of(function: ast.FunctionDef) -> list[ast.stmt]:
    body = function.body
    if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant):
        if isinstance(body[0].value.value, str):
            return body[1:]
    return body


def matches_sort(function: ast.FunctionDef, template: str) -> bool:
    if len(function.args.args) != 1:
        return False
    expected = ast.parse(template.replace('FUNCTION', function.name).replace('ARG', function.args.args[0].arg)).body[0]
    return [ast.dump(s) for s in body_of(function)] == [ast.dump(s) for s in expected.body]


def binary_comparison(function: ast.FunctionDef) -> bool:
    arguments = function.args.args
    body = body_of(function)
    return (len(arguments) == 2 and len(body) == 1 and isinstance(body[0], ast.Expr)
            and isinstance(body[0].value, ast.Compare) and len(body[0].value.ops) == 1
            and isinstance(body[0].value.ops[0], ast.Lt)
            and isinstance(body[0].value.left, ast.Name) and body[0].value.left.id == arguments[0].arg
            and isinstance(body[0].value.comparators[0], ast.Name)
            and body[0].value.comparators[0].id == arguments[1].arg)


class SupportChecker:
    def __init__(self, module: ast.Module):
        self.module = module
        self.functions = {f.name: f for f in module.body if isinstance(f, (ast.FunctionDef, ast.AsyncFunctionDef))}
        self.classes = {c.name: c for c in module.body if isinstance(c, ast.ClassDef)}
        self.bindings = set(self.functions) | set(self.classes)
        for stmt in module.body:
            if isinstance(stmt, (ast.Assign, ast.AnnAssign, ast.Import, ast.ImportFrom)):
                self.bindings.update(n.id for n in ast.walk(stmt) if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store))
                if isinstance(stmt, (ast.Import, ast.ImportFrom)):
                    self.bindings.update(a.asname or a.name.split('.')[0] for a in stmt.names)
        self.cache: dict[str, tuple[UnsupportedConstruct, ...]] = {}

    def annotation_supported(self, annotation: ast.expr | None) -> bool:
        if annotation is None or isinstance(annotation, ast.Name):
            return True
        if isinstance(annotation, ast.Constant):
            return annotation.value is None or isinstance(annotation.value, str)
        return (isinstance(annotation, ast.Subscript) and isinstance(annotation.value, ast.Name)
                and annotation.value.id == 'list' and isinstance(annotation.slice, ast.Name))

    def check(self, name: str, stack: tuple[str, ...] = ()) -> tuple[UnsupportedConstruct, ...]:
        if name in stack:
            return (UnsupportedConstruct(name, self.functions[name].lineno, 'recursive calls outside a recognized sorting implementation are unsupported', stack),)
        if name in self.cache:
            return tuple(UnsupportedConstruct(issue.function, issue.line, issue.reason,
                (*stack, *issue.dependency)) for issue in self.cache[name])
        function = self.functions.get(name)
        if function is None:
            return (UnsupportedConstruct(name, 1, f'function {name!r} is not defined in this module', stack),)
        issues: list[UnsupportedConstruct] = []
        def reject(node: ast.AST, reason: str):
            issues.append(UnsupportedConstruct(name, getattr(node, 'lineno', function.lineno), reason, stack))
        if isinstance(function, ast.AsyncFunctionDef):
            reject(function, 'async functions are unsupported')
        if function.decorator_list:
            reject(function, 'decorated functions are unsupported')
        if not self.annotation_supported(function.returns):
            reject(function.returns, 'this return annotation is unsupported by the AST model')
        args = function.args
        if args.posonlyargs or args.vararg or args.kwonlyargs or args.kwarg or args.defaults:
            reject(function, 'only plain positional arguments without defaults or variadics are supported')
        if issues:
            return tuple(issues)
        arguments = args.args
        is_list = len(arguments) == 1 and (
            isinstance(arguments[0].annotation, ast.Name) and arguments[0].annotation.id == 'list'
            or isinstance(arguments[0].annotation, ast.Subscript) and isinstance(arguments[0].annotation.value, ast.Name)
            and arguments[0].annotation.value.id == 'list')
        if is_list:
            annotation = arguments[0].annotation
            if isinstance(annotation, ast.Subscript) and not (
                isinstance(annotation.slice, ast.Name)
                and (annotation.slice.id == 'int' or annotation.slice.id in self.classes)
            ):
                reject(arguments[0], 'list element annotation needs int or a modeled object class')
            elif isinstance(annotation, ast.Subscript) and annotation.slice.id in self.classes:
                cls = self.classes[annotation.slice.id]
                issues.extend(self.check_class(cls, ('__eq__', '__lt__', '__le__', '__gt__', '__ge__'), (*stack, name)))
                if not self.is_integer_wrapper(cls):
                    reject(arguments[0], 'typed object lists require a constructor storing an integer value and direct value comparisons')
            body = body_of(function)
            if matches_sort(function, MERGE_SORT) or matches_sort(function, QUICK_SORT):
                if 'len' in self.bindings or arguments[0].arg in ('len', function.name):
                    reject(function, 'shadowing len or the recursive function is unsupported by the sorting model')
                operators = ('__le__',) if matches_sort(function, MERGE_SORT) else ('__lt__', '__gt__')
                for cls in self.classes.values():
                    issues.extend(self.check_class(cls, operators, (*stack, name)))
            elif (len(body) == 1 and isinstance(body[0], ast.Return) and isinstance(body[0].value, ast.Call)
                    and isinstance(body[0].value.func, ast.Name) and not body[0].value.keywords
                    and len(body[0].value.args) == 1 and isinstance(body[0].value.args[0], ast.Name)
                    and body[0].value.args[0].id == arguments[0].arg):
                target = body[0].value.func.id
                if target not in self.functions:
                    reject(body[0], f'call to {target!r} is unsupported')
                else:
                    issues.extend(self.check(target, (*stack, name)))
                    if not any(matches_sort(self.functions[target], template) for template in (MERGE_SORT, QUICK_SORT)):
                        reject(body[0], 'the list model supports only one delegation directly to a sorting implementation')
            else:
                reject(function, 'list programs must match a supported merge-sort or quick-sort body, or a unary delegation to one; this body does not match')
        else:
            env: dict[str, frozenset[str]] = {}
            # The binary-comparison abstraction explicitly supports untyped operands.
            body = body_of(function)
            binary = binary_comparison(function)
            for arg in arguments:
                if isinstance(arg.annotation, ast.Name) and arg.annotation.id in ('int', 'str', 'bool'):
                    env[arg.arg] = frozenset([arg.annotation.id])
                elif arg.annotation is None and binary:
                    env[arg.arg] = frozenset(['int', 'str'])
                else:
                    reject(arg, f'argument {arg.arg!r} needs a supported int, str, bool, or list annotation')
            if not issues and not (binary and any(arg.annotation is None for arg in arguments)):
                self.block(body, env, name, reject, stack)
        result = tuple(dict.fromkeys(issues))
        if not stack:
            self.cache[name] = result
        return result

    @staticmethod
    def is_integer_wrapper(cls: ast.ClassDef) -> bool:
        """Match the legacy typed-object list model's required method bodies."""
        methods = {m.name: m for m in cls.body if isinstance(m, ast.FunctionDef)}
        init = methods.get('__init__')
        if init is None or len(init.args.args) != 2:
            return False
        self_name, value = init.args.args
        if not isinstance(value.annotation, ast.Name) or value.annotation.id != 'int':
            return False
        expected = ast.parse(f'{self_name.arg}.value = {value.arg}').body
        if [ast.dump(s) for s in init.body] != [ast.dump(s) for s in expected]:
            return False
        for name, operator in (('__eq__', '=='), ('__lt__', '<'), ('__le__', '<='), ('__gt__', '>'), ('__ge__', '>=')):
            method = methods.get(name)
            if method is None or len(method.args.args) != 2:
                return False
            left, right = method.args.args
            expected = ast.parse(f'return {left.arg}.value {operator} {right.arg}.value').body
            if [ast.dump(s) for s in method.body] != [ast.dump(s) for s in expected]:
                return False
        return True

    def check_class(self, cls: ast.ClassDef, operators: tuple[str, ...], stack: tuple[str, ...]) -> list[UnsupportedConstruct]:
        issues: list[UnsupportedConstruct] = []
        methods = {m.name: m for m in cls.body if isinstance(m, ast.FunctionDef)}
        relevant = [methods[name] for name in operators if name in methods]
        if not relevant:
            return issues
        def reject(node: ast.AST, reason: str):
            issues.append(UnsupportedConstruct(cls.name, getattr(node, 'lineno', cls.lineno), reason, stack))
        if cls.bases or cls.keywords or cls.decorator_list:
            reject(cls, 'inheritance, class keywords, and class decorators are unsupported by comparison execution')
        if any(name in methods for name in ('__getattribute__', '__getattr__', '__setattr__', '__new__', 'value')):
            reject(cls, 'custom object creation or attribute behavior is unsupported by comparison execution')
        init = methods.get('__init__')
        fields: set[str] = set()
        if init:
            args = init.args.args
            body = body_of(init)
            empty = len(args) == 1 and all(isinstance(s, ast.Pass) for s in body)
            field = (len(args) == 2 and len(body) == 1 and isinstance(body[0], ast.Assign)
                     and len(body[0].targets) == 1 and isinstance(body[0].targets[0], ast.Attribute)
                     and isinstance(body[0].targets[0].value, ast.Name)
                     and body[0].targets[0].value.id == args[0].arg and body[0].targets[0].attr == 'value'
                     and isinstance(body[0].value, ast.Name) and body[0].value.id == args[1].arg
                     and isinstance(args[1].annotation, ast.Name) and args[1].annotation.id == 'int')
            if field:
                fields.add('value')
            if not (empty or field) or init.decorator_list or init.args.defaults or init.args.vararg or init.args.kwarg or init.args.kwonlyargs or init.args.posonlyargs:
                reject(init, 'only an empty constructor or storing one integer value field is supported')
        for method in relevant:
            if (len(method.args.args) != 2 or method.args.vararg or method.args.kwarg or method.args.kwonlyargs
                    or method.args.defaults or method.args.posonlyargs or method.decorator_list):
                reject(method, f'{method.name} must have exactly two plain positional arguments')
                continue
            if not self.annotation_supported(method.returns) or any(
                not self.annotation_supported(arg.annotation) for arg in method.args.args
            ):
                reject(method, f'{method.name} has an annotation unsupported by the AST model')
            env = {f'{arg.arg}.{field}': frozenset(['int']) for arg in method.args.args for field in fields}
            self.block(body_of(method), env, f'{cls.name}.{method.name}', reject, (*stack, f'{cls.name}.{method.name}'))
        return issues

    def expression(self, expr: ast.expr | None, env: dict[str, frozenset[str]], reject) -> frozenset[str]:
        if expr is None:
            return frozenset(['none'])
        if isinstance(expr, ast.Constant):
            kind = {int: 'int', bool: 'bool', str: 'str', type(None): 'none'}.get(type(expr.value))
            if kind:
                return frozenset([kind])
        elif isinstance(expr, ast.Name):
            if expr.id in env:
                return env[expr.id]
            reject(expr, f'unbound or possibly unbound variable {expr.id!r} is unsupported')
            return frozenset()
        elif isinstance(expr, ast.Attribute) and isinstance(expr.value, ast.Name):
            key = f'{expr.value.id}.{expr.attr}'
            if key in env:
                return env[key]
            reject(expr, f'attribute access {key!r} is unsupported; only initialized integer value fields are modeled')
            return frozenset()
        elif isinstance(expr, ast.BinOp):
            left = self.expression(expr.left, env, reject)
            right = self.expression(expr.right, env, reject)
            if isinstance(expr.op, (ast.Add, ast.Sub, ast.Mult, ast.FloorDiv, ast.Mod)) and left <= {'int'} and right <= {'int'}:
                if isinstance(expr.op, (ast.FloorDiv, ast.Mod)) and not (
                    isinstance(expr.right, ast.Constant) and type(expr.right.value) is int and expr.right.value >= 0
                ):
                    reject(expr, 'division and modulo currently require a nonnegative integer literal divisor')
                return frozenset(['int'])
            reject(expr, f'{type(expr.op).__name__} on these operand types is unsupported')
            return frozenset()
        elif isinstance(expr, ast.UnaryOp):
            operand = self.expression(expr.operand, env, reject)
            if isinstance(expr.op, ast.Not):
                return frozenset(['bool'])
            if isinstance(expr.op, ast.USub) and operand <= {'int'}:
                return frozenset(['int'])
        elif isinstance(expr, ast.Compare):
            if len(expr.ops) != 1:
                reject(expr, 'chained comparisons are unsupported')
                return frozenset()
            left = self.expression(expr.left, env, reject)
            right = self.expression(expr.comparators[0], env, reject)
            op = expr.ops[0]
            if isinstance(op, (ast.Eq, ast.NotEq)):
                return frozenset(['bool'])
            if isinstance(op, (ast.Lt, ast.LtE, ast.Gt, ast.GtE)) and (
                    left <= {'int', 'bool'} and right <= {'int', 'bool'} or left <= {'str'} and right <= {'str'}):
                return frozenset(['bool'])
            reject(expr, 'this ordering comparison is unsupported for the possible operand types')
            return frozenset()
        elif isinstance(expr, ast.Call):
            reject(expr, f'call to {ast.unparse(expr.func)!r} is unsupported by scalar execution')
            return frozenset()
        reject(expr, f'{type(expr).__name__} expressions are unsupported by scalar execution')
        return frozenset()

    @staticmethod
    def join(left: dict[str, frozenset[str]], right: dict[str, frozenset[str]]) -> dict[str, frozenset[str]]:
        return {name: left[name] | right[name] for name in left.keys() & right.keys()}

    def block(self, body: list[ast.stmt], env: dict[str, frozenset[str]], name: str, reject, stack: tuple[str, ...]):
        env = env.copy()
        for stmt in body:
            if isinstance(stmt, ast.Pass):
                continue
            if isinstance(stmt, (ast.Return, ast.Expr)):
                self.expression(stmt.value, env, reject)
            elif isinstance(stmt, ast.Assign) and len(stmt.targets) == 1 and isinstance(stmt.targets[0], ast.Name):
                env[stmt.targets[0].id] = self.expression(stmt.value, env, reject)
            elif isinstance(stmt, ast.AugAssign) and isinstance(stmt.target, ast.Name):
                expr = ast.copy_location(ast.BinOp(left=stmt.target, op=stmt.op, right=stmt.value), stmt)
                env[stmt.target.id] = self.expression(expr, env, reject)
            elif isinstance(stmt, ast.If):
                self.expression(stmt.test, env, reject)
                env = self.join(self.block(stmt.body, env, name, reject, stack), self.block(stmt.orelse, env, name, reject, stack))
            elif isinstance(stmt, (ast.While, ast.For)):
                if isinstance(stmt, ast.For):
                    call = stmt.iter
                    if not (isinstance(stmt.target, ast.Name) and isinstance(call, ast.Call) and isinstance(call.func, ast.Name)
                            and call.func.id == 'range' and len(call.args) == 1 and not call.keywords
                            and 'range' not in self.bindings and 'range' not in env):
                        reject(stmt, 'only for name in range(stop) is supported by scalar execution')
                        continue
                    kind = self.expression(call.args[0], env, reject)
                    if not kind <= {'int'}:
                        reject(call, 'range stop must be an integer')
                before = env.copy()
                # Finite abstract interpretation: loop variables may change type.
                while True:
                    loop_env = env.copy()
                    if isinstance(stmt, ast.For):
                        loop_env[stmt.target.id] = frozenset(['int'])
                    else:
                        self.expression(stmt.test, loop_env, reject)
                    after = self.block(stmt.body, loop_env, name, reject, stack)
                    joined = self.join(before, self.join(env, after))
                    if joined == env:
                        break
                    env = joined
                env = self.block(stmt.orelse, env, name, reject, stack)
            elif isinstance(stmt, ast.Raise) and stmt.exc is not None and stmt.cause is None:
                expr = stmt.exc
                target = expr.func if isinstance(expr, ast.Call) else expr
                cls = getattr(builtins, target.id, None) if isinstance(target, ast.Name) else None
                if not isinstance(cls, type) or not issubclass(cls, BaseException) or target.id in self.bindings or target.id in env:
                    reject(stmt, 'only builtin exception constructors are supported in raise')
                if isinstance(expr, ast.Call):
                    if expr.keywords:
                        reject(expr, 'keyword exception arguments are unsupported')
                    for arg in expr.args:
                        # scalarException currently cannot propagate an exception in an argument.
                        if any(isinstance(node, ast.BinOp) and isinstance(node.op, (ast.FloorDiv, ast.Mod)) for node in ast.walk(arg)):
                            reject(arg, 'division or modulo in exception-constructor arguments is unsupported')
                        self.expression(arg, env, reject)
            else:
                reject(stmt, f'{type(stmt).__name__} statements are unsupported by scalar execution')
        return env

    def requirement(self, name: str | None, marker: str) -> tuple[UnsupportedConstruct, ...]:
        """Check the enclosing function and any explicitly named proof dependencies."""
        issues = list(self.check(name)) if name else []
        if name:
            function = self.functions[name]
            args = function.args.args
            unary_int = len(args) == 1 and isinstance(args[0].annotation, ast.Name) and args[0].annotation.id == 'int'
            unary_list = len(args) == 1 and (
                isinstance(args[0].annotation, ast.Name) and args[0].annotation.id == 'list'
                or isinstance(args[0].annotation, ast.Subscript) and isinstance(args[0].annotation.value, ast.Name)
                and args[0].annotation.value.id == 'list')
            # A modeled body does not imply every older property has a model for its signature.
            short = marker
            while short.startswith('Not '):
                short = short[4:]
            property_name = short.split('(', 1)[0].strip()
            if property_name in ('Equiv', 'EquivReturn', 'ReturnType') and not (unary_int or unary_list):
                issues.append(UnsupportedConstruct(name, function.lineno, f'{property_name} currently supports unary int or list functions only'))
            binary_throws = binary_comparison(function) and all(
                arg.annotation is None or isinstance(arg.annotation, ast.Name) and arg.annotation.id in ('int', 'str')
                for arg in args)
            if property_name == 'Throws' and not (unary_int or unary_list or binary_throws):
                issues.append(UnsupportedConstruct(name, function.lineno, 'Throws has no function model for this argument signature'))
            if property_name == 'ReturnType' and (unary_int or unary_list) and (
                function.returns is None or ast.dump(args[0].annotation) != ast.dump(function.returns)
            ):
                issues.append(UnsupportedConstruct(name, function.lineno, 'ReturnType currently requires matching supported argument and return annotations'))
            wants_execution = property_name in ('Returns', 'Halts') or bool(re.search(r'\b(?:Returns|Halts|Throws|diverges)\(', marker))
            if unary_list and (wants_execution or property_name == 'Throws') and not matches_sort(function, MERGE_SORT):
                issues.append(UnsupportedConstruct(name, function.lineno, 'list execution currently supports only the exact merge-sort body'))
        targets = re.findall(r'\bEquiv(?:Return)?\(\s*([A-Za-z_][A-Za-z_0-9]*)\s*\)', marker)
        # Explicit low-level calls in raw requirements are checked too.
        executions = re.findall(r'\b(scalarFunction|listFunction)\s+\S+\.module\s+"([^"]+)"', marker)
        targets += [target for _, target in executions]
        for target in dict.fromkeys(targets):
            if target != name:
                issues.extend(self.check(target, (name,) if name else ()))
                if name and target in self.functions and property_name in ('Equiv', 'EquivReturn'):
                    target_args = self.functions[target].args.args
                    if len(args) != 1 or len(target_args) != 1 or (
                        ast.dump(args[0].annotation or ast.Constant(None)) !=
                        ast.dump(target_args[0].annotation or ast.Constant(None))
                    ):
                        issues.append(UnsupportedConstruct(target, self.functions[target].lineno,
                            f'{property_name} requires matching supported argument domains', (name,)))
        for model, target in executions:
            function = self.functions.get(target)
            if function is None:
                continue
            if model == 'listFunction' and not matches_sort(function, MERGE_SORT):
                issues.append(UnsupportedConstruct(target, function.lineno,
                    'list execution currently supports only the exact merge-sort body'))
            if model == 'scalarFunction' and any(not (
                isinstance(arg.annotation, ast.Name) and arg.annotation.id in ('int', 'str', 'bool')
            ) for arg in function.args.args):
                issues.append(UnsupportedConstruct(target, function.lineno,
                    'scalar execution requires scalar int, str, or bool arguments'))
        properties = re.findall(
            r'\b(EquivReturn|Equiv|ReturnType|Throws)\s+\S+\.module\s+"([^"]+)"(?:\s+"([^"]+)")?', marker)
        for prop, target, other in properties:
            if target in self.functions:
                issues.extend(self.requirement(target, f'{prop}({other})' if other else prop))
            else:
                issues.extend(self.check(target))
        for class_name in re.findall(r'\.object\s+"([^"]+)"', marker):
            if class_name not in self.classes:
                issues.append(UnsupportedConstruct(name or '<module>', self.functions[name].lineno if name else 1,
                    f'object class {class_name!r} is not defined in this module'))
            else:
                issues.extend(self.check_class(self.classes[class_name],
                    ('__lt__', '__le__', '__gt__', '__ge__', '__eq__', '__ne__'), (name,) if name else ()))
        return tuple(dict.fromkeys(issues))
