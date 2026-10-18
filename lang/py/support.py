"""Conservative source coverage checks for FormalSW's supported Python models.

A requirement is rejected if any part of its function or a modeled dependency
falls outside the selected model. Both branches and unreachable statements are
checked; sampling inputs or executing the Python program is never used.
"""
from __future__ import annotations

import ast
import builtins
import re
from dataclasses import dataclass
from lang.py.global_inputs import function_globals, GlobalInputError, annotation_kind
from lang.py.mutable_support import check_mutable
from lang.py.sorting_support import MERGE_SORT, QUICK_SORT, body_of, matches_sort
from lang.py.call_support import uses_parallel_model, check_calls, uses_calls_model, uses_heap_calls, uses_builtin, uses_method, uses_library_calls, uses_bytes, uses_assertions


@dataclass(frozen=True)
class UnsupportedConstruct:
    function: str
    line: int
    reason: str
    dependency: tuple[str, ...] = ()


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
        if (isinstance(annotation, ast.Subscript) and isinstance(annotation.value, ast.Name)
                and annotation.value.id == 'list' and isinstance(annotation.slice, ast.Name)
                and annotation.slice.id in self.classes):
            # The legacy object-sorting model validates the class methods below.
            return True
        return annotation_kind(annotation) is not None

    def check(self, name: str, stack: tuple[str, ...] = (), *, parallel: bool = False, mutable: bool = False, heap_calls: bool = False) -> tuple[UnsupportedConstruct, ...]:
        if name in stack:
            return (UnsupportedConstruct(name, self.functions[name].lineno, 'recursive calls outside a recognized sorting implementation are unsupported', stack),)
        if name in self.cache and not parallel and not mutable and not heap_calls:
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
        if getattr(function, 'type_params', []):
            reject(function, 'generic function scopes are unsupported')
        if not self.annotation_supported(function.returns):
            reject(function.returns, 'this return annotation is unsupported by the AST model')
        args = function.args
        if args.posonlyargs or args.vararg or args.kwonlyargs or args.kwarg:
            reject(function, 'only plain positional arguments without variadics are supported')
        if args.defaults and (mutable or parallel or uses_parallel_model(function)
                              or not heap_calls and not uses_calls_model(self.module, function)):
            reject(function, 'default arguments currently require scalar call execution')
        if issues:
            return tuple(issues)
        if parallel or uses_parallel_model(function):
            self.check_parallel(function, reject)
            return tuple(dict.fromkeys(issues))
        try:
            globals = function_globals(self.module, function)
        except GlobalInputError as error:
            return (UnsupportedConstruct(name, error.line, str(error), stack),)
        if heap_calls and globals:
            reject(function, 'heap call execution does not support globals')
            return tuple(issues)
        if mutable or any(item.kind.startswith('list[') for item in globals):
            check_mutable(function, globals, self.bindings, reject)
            result = tuple(dict.fromkeys(issues))
            if not stack and not mutable:
                self.cache[name] = result
            return result
        if heap_calls or (uses_calls_model(self.module, function) and uses_heap_calls(self.module, function)):
            check_calls(self.module, function, reject, heap=True)
            return tuple(dict.fromkeys(issues))
        if uses_calls_model(self.module, function):
            check_calls(self.module, function, reject)
            return tuple(dict.fromkeys(issues))
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
            try:
                env.update((item.name, frozenset([item.kind])) for item in function_globals(self.module, function))
            except GlobalInputError as error:
                issues.append(UnsupportedConstruct(name, error.line, str(error), stack))
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

    def check_parallel(self, function: ast.FunctionDef, reject) -> None:
        """Validate heap operations, local values, plain objects, and mutex bindings."""
        required_primitives = set()
        env: dict[str, frozenset[str]] = {}
        fields: dict[str, dict[str, frozenset[str]]] = {}

        def plain_class(name):
            if name in fields:
                return
            fields[name] = {}
            cls = self.classes[name]
            if cls.bases or cls.keywords or cls.decorator_list:
                reject(cls, 'parallel objects must be plain classes without inheritance or decorators')
            for member in body_of(cls):
                if isinstance(member, ast.FunctionDef) and member.name == '__init__':
                    if (not member.args.args or member.decorator_list or member.args.defaults
                            or member.args.posonlyargs or member.args.vararg or member.args.kwonlyargs or member.args.kwarg):
                        reject(member, 'parallel object constructors require plain positional arguments')
                        continue
                    self_name = member.args.args[0].arg
                    params = {arg.arg for arg in member.args.args[1:]}
                    for statement in body_of(member):
                        if isinstance(statement, ast.Pass):
                            continue
                        if (isinstance(statement, ast.Assign) and len(statement.targets) == 1
                                and isinstance(statement.targets[0], ast.Attribute)
                                and isinstance(statement.targets[0].value, ast.Name)
                                and statement.targets[0].value.id == self_name
                                and not statement.targets[0].attr.startswith('__')
                                and (isinstance(statement.value, ast.Constant) and type(statement.value.value) in (int, bool, str, type(None))
                                     or isinstance(statement.value, ast.Name) and statement.value.id in params)):
                            value = statement.value
                            kind = 'reference'
                            if isinstance(value, ast.Constant):
                                kind = {int: 'int', bool: 'bool', str: 'str', type(None): 'reference'}[type(value.value)]
                            elif isinstance(value, ast.Name):
                                parameter = next(arg for arg in member.args.args if arg.arg == value.id)
                                if isinstance(parameter.annotation, ast.Name) and parameter.annotation.id in ('int', 'str', 'bool'):
                                    kind = parameter.annotation.id
                            fields[name][statement.targets[0].attr] = (
                                frozenset(['reference', 'none']) if kind == 'reference' else frozenset([kind]))
                        else:
                            reject(statement, 'parallel object constructors may only initialize plain fields from constants or arguments')
                else:
                    reject(member, 'parallel objects currently support plain data fields and an __init__ method only')

        for arg in function.args.args:
            annotation = arg.annotation
            if isinstance(annotation, ast.Name) and annotation.id in ('int', 'str', 'bool'):
                env[arg.arg] = frozenset([annotation.id])
            elif isinstance(annotation, ast.Name) and annotation.id == 'Lock':
                env[arg.arg] = frozenset(['lock'])
                required_primitives.add(('Lock', 'threading'))
            elif isinstance(annotation, ast.Name) and annotation.id in self.classes:
                plain_class(annotation.id)
                env[arg.arg] = frozenset(['object:' + annotation.id])
            elif (isinstance(annotation, ast.Subscript) and isinstance(annotation.value, ast.Name)
                    and annotation.value.id == 'list' and isinstance(annotation.slice, ast.Name)
                    and annotation.slice.id in ('int', 'str', 'bool')):
                env[arg.arg] = frozenset(['array:' + annotation.slice.id])
            else:
                reject(arg, 'parallel arguments need scalar, list[int/str/bool], plain object, or Lock annotations')
        if any(name in env for name in ('Lock', 'sleep')):
            reject(function, 'parallel arguments must not shadow Lock or sleep')

        def pure(expr):
            if isinstance(expr, ast.Constant) and type(expr.value) in (int, bool, str, type(None)):
                return frozenset([{int: 'int', bool: 'bool', str: 'str', type(None): 'none'}[type(expr.value)]])
            if isinstance(expr, ast.Name):
                if expr.id in env:
                    return env[expr.id]
                reject(expr, f'unbound local {expr.id!r} in parallel execution')
                return frozenset()
            if isinstance(expr, ast.Compare):
                if len(expr.ops) != 1:
                    reject(expr, 'parallel comparisons currently support one operator at a time')
                kinds = pure(expr.left)
                for operand in expr.comparators:
                    kinds |= pure(operand)
                if not kinds <= {'int', 'str', 'bool', 'none'}:
                    reject(expr, 'parallel comparisons require local scalars')
                return self.expression(expr, env, reject)
            if isinstance(expr, ast.UnaryOp) and isinstance(expr.op, ast.Not):
                if not pure(expr.operand) <= {'int', 'str', 'bool', 'none'}:
                    reject(expr, 'parallel truth tests require local scalars')
                return frozenset(['bool'])
            if isinstance(expr, (ast.BinOp, ast.UnaryOp)):
                # Reuse the conservative scalar arithmetic validator, with no heap reads.
                if any(isinstance(node, (ast.Attribute, ast.Subscript, ast.Call, ast.Compare)) for node in ast.walk(expr)):
                    reject(expr, 'parallel arithmetic must use local scalar values; split shared reads into separate statements')
                    return frozenset()
                if isinstance(expr, ast.UnaryOp) and not isinstance(expr.op, ast.USub):
                    reject(expr, 'parallel unary expressions currently support integer negation only')
                    return frozenset()
                return self.expression(expr, env, reject)
            reject(expr, 'parallel expressions require local values; split shared accesses into separate statements')
            return frozenset()

        def location(expr):
            if isinstance(expr, ast.Subscript):
                base = pure(expr.value)
                index = pure(expr.slice)
                if not index <= {'int'}:
                    reject(expr, 'parallel list indices must be integers')
                if not all(kind.startswith('array:') for kind in base):
                    reject(expr, 'parallel indexing requires a list reference')
                return frozenset(kind.removeprefix('array:') for kind in base)
            if isinstance(expr, ast.Attribute):
                base = pure(expr.value)
                if expr.attr.startswith('__'):
                    reject(expr, 'special attributes are unsupported in parallel execution')
                for kind in base:
                    if kind.startswith('object:'):
                        name = kind.removeprefix('object:')
                        if expr.attr not in fields[name]:
                            reject(expr, f'{name}.{expr.attr} is not a declared plain field')
                    elif kind not in ('reference', 'none'):
                        reject(expr, 'parallel field access requires an object reference')
                possible = []
                for kind in base:
                    if kind.startswith('object:'):
                        possible.append(fields[kind.removeprefix('object:')].get(expr.attr, frozenset()))
                    elif kind == 'reference':
                        possible.extend(record[expr.attr] for record in fields.values() if expr.attr in record)
                return frozenset().union(*possible) if possible else frozenset(['reference', 'none'])
            reject(expr, 'parallel assignments require a local, list item, or plain object field')
            return frozenset()

        def block(body, initial):
            nonlocal env
            env = initial.copy()
            for statement in body:
                if isinstance(statement, ast.If):
                    if not pure(statement.test) <= {'int', 'str', 'bool', 'none'}:
                        reject(statement.test, 'parallel truth tests require local scalars')
                    before = env.copy()
                    yes = block(statement.body, before)
                    no = block(statement.orelse, before)
                    env = self.join(yes, no)
                    continue
                if isinstance(statement, ast.While):
                    before = env.copy()
                    while True:
                        if not pure(statement.test) <= {'int', 'str', 'bool', 'none'}:
                            reject(statement.test, 'parallel truth tests require local scalars')
                        current = env.copy()
                        after = block(statement.body, current)
                        joined = self.join(before, self.join(current, after))
                        env = joined
                        if joined == current:
                            break
                    env = block(statement.orelse, env)
                    continue
                if isinstance(statement, ast.Pass):
                    continue
                if isinstance(statement, ast.Assign) and len(statement.targets) == 1:
                    target = statement.targets[0]
                    if isinstance(target, ast.Name):
                        if target.id in ('Lock', 'sleep'):
                            reject(statement, 'parallel locals must not shadow Lock or sleep')
                        env[target.id] = location(statement.value) if isinstance(statement.value, (ast.Attribute, ast.Subscript)) else pure(statement.value)
                        continue
                    target_kind = location(target)
                    value_kind = pure(statement.value)
                    if isinstance(target, ast.Subscript) and not value_kind <= target_kind:
                        reject(statement, 'parallel list writes must preserve the annotated element type')
                    if isinstance(target, ast.Attribute):
                        normalized = frozenset('reference' if kind.startswith(('object:', 'array:')) else kind for kind in value_kind)
                        if not normalized <= target_kind:
                            reject(statement, 'parallel field writes must preserve the declared scalar or reference layout')
                    continue
                if isinstance(statement, ast.Expr) and isinstance(statement.value, ast.Call):
                    call = statement.value
                    if not call.keywords:
                        if isinstance(call.func, ast.Attribute) and call.func.attr in ('acquire', 'release') and not call.args:
                            if pure(call.func.value) != frozenset(['lock']):
                                reject(call, 'acquire/release requires a mutex reference')
                            required_primitives.add(('Lock', 'threading'))
                            continue
                        if (isinstance(call.func, ast.Name) and call.func.id == 'sleep' and len(call.args) == 1
                                and isinstance(call.args[0], ast.Constant) and type(call.args[0].value) is int and call.args[0].value == 0):
                            required_primitives.add(('sleep', 'time'))
                            continue
                reject(statement, 'parallel execution supports local assignments, separate heap reads/writes, acquire/release, sleep(0), scalar if/while, and pass only')

            return env.copy()

        block(body_of(function), env)

        for primitive, module in sorted(required_primitives):
            definitions = []
            for statement in self.module.body:
                if isinstance(statement, ast.ImportFrom):
                    for alias in statement.names:
                        if (alias.asname or alias.name) == primitive:
                            definitions.append(statement.level == 0 and statement.module == module and alias.name == primitive)
                elif isinstance(statement, ast.Import):
                    definitions.extend(False for alias in statement.names if (alias.asname or alias.name.split('.')[0]) == primitive)
                elif isinstance(statement, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                    if statement.name == primitive:
                        definitions.append(False)
                else:
                    definitions.extend(False for node in ast.walk(statement)
                                       if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store) and node.id == primitive)
            if definitions != [True]:
                reject(function, f'parallel execution requires an unshadowed from {module} import {primitive}')

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
            if isinstance(stmt, (ast.Pass, ast.Global)):
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

    @staticmethod
    def execution_targets(marker: str):
        return re.findall(r'\b(HeapCalls\.call|HeapCalls\.scalarFunction|Calls\.function|Mutable\.function|scalarFunctionWithGlobals|scalarFunction|listFunction|parallelFunction)\s+(?:\S+\.module|_this_module)\s+"([^"]+)"', marker)

    def requirement(self, name: str | None, marker: str) -> tuple[UnsupportedConstruct, ...]:
        """Check the enclosing function and any explicitly named proof dependencies."""
        mutable = False
        candidates = ([name] if name else []) + re.findall(r'\bEquiv(?:Return)?\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)', marker)
        try:
            mutable = any(item.kind.startswith('list[') for target in candidates if target in self.functions
                          for item in function_globals(self.module, self.functions[target]))
        except GlobalInputError:
            pass
        explicit_heap = any(model == "HeapCalls.call" and target == name
                            for model, target in self.execution_targets(marker))
        issues = list(self.check(name, mutable=mutable, heap_calls=explicit_heap)) if name else []
        if name:
            function = self.functions[name]
            if uses_parallel_model(function) and (
                not marker.startswith('theorem ') or (re.search(r'\b(?:Returns|Halts|Throws|diverges)\(', marker) and not re.search(r'\bParallel\(', marker))
            ):
                issues.append(UnsupportedConstruct(name, function.lineno,
                    'concurrent workers require a raw Parallel specification or a quoted Python trial'))
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
            if uses_calls_model(self.module, function) and property_name not in ('Returns', 'Halts') and not marker.startswith('theorem '):
                issues.append(UnsupportedConstruct(name, function.lineno,
                    'call execution requires a raw theorem for this property; legacy abstract properties do not model calls'))
            try:
                global_targets = re.findall(r'\bEquiv(?:Return)?\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)', marker)
                stateful = bool(function_globals(self.module, function)) or any(
                    function_globals(self.module, self.functions[target])
                    for target in global_targets if target in self.functions)
            except GlobalInputError:
                stateful = False  # check() reports the precise declaration error.
            supported_arguments = all(annotation_kind(arg.annotation) is not None for arg in args)
            if stateful and property_name == 'BigO':
                issues.append(UnsupportedConstruct(name, function.lineno,
                    'BigO does not yet model global-state inputs; use an explicit cost specification'))
            if property_name in ('Equiv', 'EquivReturn', 'ReturnType') and not (
                    unary_int or unary_list or stateful and supported_arguments):
                issues.append(UnsupportedConstruct(name, function.lineno, f'{property_name} currently supports unary int or list functions only'))
            binary_throws = binary_comparison(function) and all(
                arg.annotation is None or isinstance(arg.annotation, ast.Name) and arg.annotation.id in ('int', 'str')
                for arg in args)
            if property_name == 'Throws' and not (unary_int or unary_list or binary_throws or stateful and supported_arguments):
                issues.append(UnsupportedConstruct(name, function.lineno, 'Throws has no function model for this argument signature'))
            if property_name == 'ReturnType' and not stateful and (unary_int or unary_list) and (
                function.returns is None or ast.dump(args[0].annotation) != ast.dump(function.returns)
            ):
                issues.append(UnsupportedConstruct(name, function.lineno, 'ReturnType currently requires matching supported argument and return annotations'))
            if property_name == 'ReturnType' and stateful and not (
                annotation_kind(function.returns) is not None
                or isinstance(function.returns, ast.Constant) and function.returns.value is None
            ):
                issues.append(UnsupportedConstruct(name, function.lineno,
                    'ReturnType with globals requires a supported scalar, scalar-list, or None return annotation'))
            wants_execution = property_name in ('Returns', 'Halts') or bool(re.search(r'\b(?:Returns|Halts|Throws|diverges)\(', marker))
            if unary_list and not stateful and not explicit_heap and not uses_calls_model(self.module, function) and (wants_execution or property_name == 'Throws') and not matches_sort(function, MERGE_SORT):
                issues.append(UnsupportedConstruct(name, function.lineno, 'list execution currently supports only the exact merge-sort body'))
        targets = re.findall(r'\bEquiv(?:Return)?\(\s*([A-Za-z_][A-Za-z_0-9]*)\s*\)', marker)
        # Explicit low-level calls in raw requirements are checked too.
        executions = self.execution_targets(marker)
        parallel_targets = {target for model, target in executions if model == 'parallelFunction'}
        targets += [target for _, target in executions]
        for target in dict.fromkeys(targets):
            if target != name:
                issues.extend(self.check(target, (name,) if name else (), parallel=target in parallel_targets, mutable=mutable or ("Mutable.function", target) in executions))
                if name and target in self.functions and property_name in ('Equiv', 'EquivReturn'):
                    target_args = self.functions[target].args.args
                    if len(args) != len(target_args) or any(
                        ast.dump(a.annotation or ast.Constant(None)) != ast.dump(b.annotation or ast.Constant(None))
                        for a, b in zip(args, target_args)):
                        issues.append(UnsupportedConstruct(target, self.functions[target].lineno,
                            f'{property_name} requires matching supported argument domains', (name,)))
        for model, target in executions:
            function = self.functions.get(target)
            if function is None:
                continue
            if uses_assertions(self.module, function) and model not in ('Calls.function', 'HeapCalls.call', 'HeapCalls.scalarFunction', 'Mutable.function'):
                issues.append(UnsupportedConstruct(target, function.lineno,
                    'assertions require an interpreter that executes their conditions and messages'))
            if uses_bytes(self.module, function) and model not in ('Calls.function', 'HeapCalls.call', 'HeapCalls.scalarFunction'):
                issues.append(UnsupportedConstruct(target, function.lineno,
                    'byte literals require a call interpreter'))
            if uses_library_calls(self.module, function) and model not in ('Calls.function', 'HeapCalls.call', 'HeapCalls.scalarFunction'):
                issues.append(UnsupportedConstruct(target, function.lineno,
                    'standard-library calls require a call interpreter'))
            if uses_method(self.module, function, 'bit_length') and model not in ('Calls.function', 'HeapCalls.call', 'HeapCalls.scalarFunction'):
                issues.append(UnsupportedConstruct(target, function.lineno,
                    'int.bit_length requires a call interpreter'))
            if uses_builtin(self.module, function, 'sum') and model not in ('Calls.function', 'HeapCalls.call', 'HeapCalls.scalarFunction'):
                issues.append(UnsupportedConstruct(target, function.lineno,
                    'sums require a call interpreter'))
            if uses_builtin(self.module, function, 'int') and model not in ('Calls.function', 'HeapCalls.call', 'HeapCalls.scalarFunction'):
                issues.append(UnsupportedConstruct(target, function.lineno,
                    'integer conversion requires a call interpreter'))
            if uses_builtin(self.module, function, 'len') and model in ('scalarFunction', 'scalarFunctionWithGlobals'):
                issues.append(UnsupportedConstruct(target, function.lineno,
                    'sequence length requires a call interpreter'))
            if any(uses_builtin(self.module, function, name) for name in ('min', 'max')) and model not in ('Calls.function', 'HeapCalls.call', 'HeapCalls.scalarFunction'):
                issues.append(UnsupportedConstruct(target, function.lineno,
                    'positional min/max requires a call interpreter'))
            if (uses_calls_model(self.module, function) and uses_heap_calls(self.module, function)
                    and model not in ('HeapCalls.call', 'HeapCalls.scalarFunction', 'parallelFunction')):
                issues.append(UnsupportedConstruct(target, function.lineno,
                    'list helper calls require the heap call interpreter'))
            if model in ('HeapCalls.call', 'HeapCalls.scalarFunction'):
                if model == 'HeapCalls.scalarFunction' and any(annotation_kind(arg.annotation) not in ('int', 'str', 'bytes', 'bool') for arg in function.args.args):
                    issues.append(UnsupportedConstruct(target, function.lineno,
                        'heap-call specifications currently require scalar entry arguments'))
                kind = annotation_kind(function.returns)
                if model == 'HeapCalls.scalarFunction' and kind and (kind.startswith(('list[', 'set[')) or kind == 'bytearray'):
                    issues.append(UnsupportedConstruct(target, function.lineno,
                        f'{kind.split("[")[0]} results require HeapCalls.call rather than its scalar adapter'))
                issues.extend(self.check(target, heap_calls=True))
            if function.args.defaults and model not in ('Calls.function', 'HeapCalls.call', 'HeapCalls.scalarFunction'):
                issues.append(UnsupportedConstruct(target, function.lineno,
                    'default arguments require Calls.function execution'))
            if model == 'Mutable.function':
                issues.extend(self.check(target, mutable=True))
            if model == 'parallelFunction':
                self.check_parallel(function, lambda node, reason: issues.append(UnsupportedConstruct(
                    target, getattr(node, 'lineno', function.lineno), reason)))
            if model == 'listFunction' and not matches_sort(function, MERGE_SORT):
                issues.append(UnsupportedConstruct(target, function.lineno,
                    'list execution currently supports only the exact merge-sort body'))
            if model in ('scalarFunction', 'scalarFunctionWithGlobals') and any(not (
                isinstance(arg.annotation, ast.Name) and arg.annotation.id in ('int', 'str', 'bool')
            ) for arg in function.args.args):
                issues.append(UnsupportedConstruct(target, function.lineno,
                    'scalar execution requires scalar int, str, or bool arguments'))
            if model == 'scalarFunctionWithGlobals':
                try:
                    if any(item.kind.startswith('list[') for item in function_globals(self.module, function)):
                        issues.append(UnsupportedConstruct(target, function.lineno,
                            'mutable globals require Mutable.function with a shared heap'))
                except GlobalInputError:
                    pass
            if model == 'scalarFunction':
                try:
                    if function_globals(self.module, function):
                        issues.append(UnsupportedConstruct(target, function.lineno,
                            'globals require scalarFunctionWithGlobals with explicit initial state'))
                except GlobalInputError:
                    pass
        properties = re.findall(
            r'\b(EquivReturn|Equiv|ReturnType|Throws|BigO)\s+(?:\S+\.module|_this_module)\s+"([^"]+)"(?:\s+"([^"]+)")?', marker)
        for prop, target, other in properties:
            if target in self.functions:
                issues.extend(self.requirement(target, f'{prop}({other})' if other else prop))
                if any(uses_assertions(self.module, self.functions[f])
                       for f in (target, other) if f in self.functions):
                    issues.append(UnsupportedConstruct(target, self.functions[target].lineno,
                        'legacy Function properties omit assertions; use the short DSL or Calls'))
                if any(uses_bytes(self.module, self.functions[f])
                       for f in (target, other) if f in self.functions):
                    issues.append(UnsupportedConstruct(target, self.functions[target].lineno,
                        'legacy Function properties omit byte literals; use the short DSL or Calls'))
                if any(uses_library_calls(self.module, self.functions[f])
                       for f in (target, other) if f in self.functions):
                    issues.append(UnsupportedConstruct(target, self.functions[target].lineno,
                        'legacy Function properties omit standard-library calls; use the short DSL or Calls'))
                if any(uses_calls_model(self.module, self.functions[f]) and uses_heap_calls(self.module, self.functions[f])
                       for f in (target, other) if f in self.functions):
                    issues.append(UnsupportedConstruct(target, self.functions[target].lineno,
                        'legacy Function properties omit heap calls; use the short DSL or HeapCalls'))
                if any(uses_builtin(self.module, self.functions[f], name)
                       for f in (target, other) if f in self.functions for name in ('min', 'max')):
                    issues.append(UnsupportedConstruct(target, self.functions[target].lineno,
                        'legacy Function properties omit positional min/max; use the short DSL or Calls'))
                if any(uses_method(self.module, self.functions[f], 'bit_length')
                       for f in (target, other) if f in self.functions):
                    issues.append(UnsupportedConstruct(target, self.functions[target].lineno,
                        'legacy Function properties omit int.bit_length; use the short DSL or Calls'))
                if any(uses_builtin(self.module, self.functions[f], 'sum')
                       for f in (target, other) if f in self.functions):
                    issues.append(UnsupportedConstruct(target, self.functions[target].lineno,
                        'legacy Function properties omit range sums; use the short DSL or Calls'))
                try:
                    if any(function_globals(self.module, self.functions[f])
                           for f in (target, other) if f in self.functions):
                        issues.append(UnsupportedConstruct(target, self.functions[target].lineno,
                            'legacy Function properties omit globals; use scalarFunctionWithGlobals or a short DSL marker'))
                except GlobalInputError:
                    pass
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
