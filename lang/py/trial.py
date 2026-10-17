"""Compile setup, worker submissions, and assertions for quoted Python trials.

A trial allocates objects, submits calls to a ThreadPoolExecutor, waits for their
results, and checks Python assertions. The compiler translates statements, not
recognized data structures. The same helper is executable by the runtime demo.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass
import json


class ScenarioError(ValueError):
    pass


class ScenarioUnsupported(ScenarioError):
    def __init__(self, line: int, reason: str):
        super().__init__(reason)
        self.line = line


def quoted(value: str) -> str:
    return json.dumps(value)


def identifier(value: str) -> str:
    """Python identifiers may also be Lean keywords."""
    return f'«{value}»'


def integer_literal(node):
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return node.value
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        value = integer_literal(node.operand)
        if value is not None:
            return -value
    return None


def body_of(function):
    body = function.body
    if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) and isinstance(body[0].value.value, str):
        return body[1:]
    return body


@dataclass(frozen=True)
class Value:
    code: str
    kind: object


class TrialCompiler:
    def __init__(self, helper: str, module: ast.Module, function: ast.FunctionDef, namespace: str):
        self.module, self.function, self.namespace = module, function, namespace
        self.helper = next((n for n in module.body if isinstance(n, ast.FunctionDef) and n.name == helper), None)
        if self.helper is None:
            raise ScenarioError(f'unknown Python trial helper {helper!r}')
        self.locks = []
        self.arrays = {}
        self.allocations = {}
        self.serial = 0
        self.used_names = {n.id for n in ast.walk(self.helper) if isinstance(n, ast.Name)}
        self.used_names.update(a.arg for a in ast.walk(self.helper) if isinstance(a, ast.arg))
        self.job_name = self.unique('_job')
        self.final_name = self.unique('_final')
        self.check_header()
        statements = body_of(self.helper)
        regions = [i for i, n in enumerate(statements) if isinstance(n, ast.With)]
        if len(regions) != 1:
            self.reject(self.helper, 'a concurrent trial needs one ThreadPoolExecutor block')
        position = regions[0]
        self.setup, self.post = statements[:position], statements[position + 1:]
        for statement in self.setup:
            self.allocation(statement)
        self.call, self.loop = self.executor(statements[position])
        # Python resolves these names at runtime. Do not silently interpret a
        # rebound builtin, class, or helper as the original definition.
        reserved = {'range', 'zip', 'len', 'max', 'Lock', 'ThreadPoolExecutor',
                    helper, function.name}
        for node in ast.walk(self.helper):
            if ((isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store) and node.id in reserved)
                    or isinstance(node, ast.arg) and node.arg in reserved):
                self.reject(node, 'trial locals must not shadow constructors, helpers, or supported builtins')
        for name in {'range', 'zip', 'len', 'max', helper, function.name}:
            expected = [] if name in {'range', 'zip', 'len', 'max'} else [
                self.helper if name == helper else function]
            if self.global_bindings(name) != expected:
                self.reject(self.helper, f'trial requires an unshadowed {name}')
        primitives = [('ThreadPoolExecutor', 'concurrent.futures')]
        if self.locks:
            primitives.append(('Lock', 'threading'))
        for primitive, origin in primitives:
            bindings = []
            for node in module.body:
                if isinstance(node, ast.ImportFrom):
                    bindings.extend(node.level == 0 and node.module == origin and a.name == primitive
                                    for a in node.names if (a.asname or a.name) == primitive)
                elif isinstance(node, (ast.FunctionDef, ast.ClassDef)) and node.name == primitive:
                    bindings.append(False)
                else:
                    bindings.extend(False for n in ast.walk(node)
                                    if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store) and n.id == primitive)
            if bindings != [True]:
                self.reject(self.helper, f'trial requires an unshadowed from {origin} import {primitive}')

    def global_bindings(self, name):
        bindings = []

        def visit(node):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                if node.name == name:
                    bindings.append(node)
                return
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                if any(a.name == '*' or (a.asname or a.name.split('.')[0]) == name for a in node.names):
                    bindings.append(node)
                return
            if isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)) and node.id == name:
                bindings.append(node)
            for child in ast.iter_child_nodes(node):
                visit(child)

        visit(self.module)
        return bindings

    def reject(self, node, reason):
        raise ScenarioUnsupported(getattr(node, 'lineno', self.helper.lineno), reason)

    def unique(self, name):
        while name in self.used_names:
            name += '_'
        self.used_names.add(name)
        return name

    def fresh(self, prefix):
        self.serial += 1
        return self.unique(f'_{prefix}{self.serial}')

    def allocation(self, statement):
        if not isinstance(statement, ast.Assign) or len(statement.targets) != 1:
            return
        targets, values = [statement.targets[0]], [statement.value]
        if isinstance(targets[0], ast.Tuple) and isinstance(values[0], ast.Tuple):
            targets, values = targets[0].elts, values[0].elts
        if len(targets) != len(values):
            self.reject(statement, 'assignment tuple lengths differ')
        allocations = []
        for target, value in zip(targets, values):
            if not isinstance(target, ast.Name):
                return
            if isinstance(value, ast.Call) and isinstance(value.func, ast.Name) and not value.args and not value.keywords:
                if value.func.id == 'Lock':
                    self.locks.append(target.id)
                    allocations.append((target.id, 'lock'))
                else:
                    self.reject(value, 'quoted trials support list allocations and locks, not reference-object constructors')
            elif (isinstance(value, ast.List) and value.elts
                  and all(integer_literal(element) is not None for element in value.elts)):
                self.arrays[target.id] = [integer_literal(element) for element in value.elts]
                allocations.append((target.id, 'array'))
            else:
                if allocations:
                    self.reject(statement, 'mixed allocation and alias tuple assignments are unsupported')
                return
        self.allocations[id(statement)] = allocations

    def executor(self, statement):
        if len(statement.items) != 1:
            self.reject(statement, 'one executor per trial is currently supported')
        item = statement.items[0]
        ctor = item.context_expr
        if (not isinstance(ctor, ast.Call) or not isinstance(ctor.func, ast.Name) or ctor.func.id != 'ThreadPoolExecutor'
                or ctor.args or not isinstance(item.optional_vars, ast.Name)):
            self.reject(statement, 'use with ThreadPoolExecutor(...) as executor')
        # The model permits every worker to run; validate a positive pool
        # size here and sufficient capacity after parsing the submitted jobs.
        for keyword in ctor.keywords:
            if keyword.arg != 'max_workers' or not (
                isinstance(keyword.value, ast.Constant) and type(keyword.value.value) is int and keyword.value.value > 0
                or isinstance(keyword.value, ast.Call) and isinstance(keyword.value.func, ast.Name)
                and keyword.value.func.id == 'max' and not keyword.value.keywords and len(keyword.value.args) == 2
                and isinstance(keyword.value.args[0], ast.Constant) and type(keyword.value.args[0].value) is int
                and keyword.value.args[0].value == 1
                and (isinstance(keyword.value.args[1], ast.Name) and keyword.value.args[1].id in self.inputs
                     or isinstance(keyword.value.args[1], ast.Call) and isinstance(keyword.value.args[1].func, ast.Name)
                     and keyword.value.args[1].func.id == 'len' and not keyword.value.args[1].keywords
                     and len(keyword.value.args[1].args) == 1 and isinstance(keyword.value.args[1].args[0], ast.Name)
                     and keyword.value.args[1].args[0].id in self.arrays)
            ):
                self.reject(ctor, 'executor max_workers must be a positive literal or max(1, len(collection))')
        if len(ctor.keywords) > 1 or len(statement.body) != 2:
            self.reject(statement, 'executor block must submit a list of jobs and wait for every future.result()')
        submit, wait = statement.body
        if (not isinstance(submit, ast.Assign) or len(submit.targets) != 1 or not isinstance(submit.targets[0], ast.Name)
                or not isinstance(submit.value, ast.ListComp) or len(submit.value.generators) != 1):
            self.reject(submit, 'submit jobs with a list comprehension')
        call, loop = submit.value.elt, submit.value.generators[0]
        if (not isinstance(call, ast.Call) or not isinstance(call.func, ast.Attribute) or call.func.attr != 'submit'
                or not isinstance(call.func.value, ast.Name) or call.func.value.id != item.optional_vars.id
                or not call.args or not isinstance(call.args[0], ast.Name) or call.args[0].id != self.worker_arg or call.keywords
                or loop.ifs or loop.is_async or not isinstance(loop.target, ast.Name)):
            self.reject(submit, 'submit must call the trial worker with positional arguments')
        # Every quoted claim needs a pool that can run all submitted workers.
        capacity = ast.parse(f'max(1, len({ast.unparse(loop.iter)}))', mode='eval').body
        enough = len(ctor.keywords) == 1 and ast.dump(ctor.keywords[0].value) == ast.dump(capacity)
        if (len(ctor.keywords) == 1 and isinstance(loop.iter, ast.Call)
                and isinstance(loop.iter.func, ast.Name) and loop.iter.func.id == 'range'
                and len(loop.iter.args) == 1 and not loop.iter.keywords):
            # len(range(n)) = max(0, n), so max(1, n) admits every job.
            range_capacity = ast.Call(func=ast.Name(id='max', ctx=ast.Load()),
                                      args=[ast.Constant(value=1), loop.iter.args[0]], keywords=[])
            enough |= ast.dump(ctor.keywords[0].value) == ast.dump(range_capacity)
            count = integer_literal(loop.iter.args[0])
            pool = integer_literal(ctor.keywords[0].value)
            enough |= count is not None and pool is not None and pool >= max(0, count)
        if not enough:
            self.reject(ctor, 'quoted trials need max_workers=max(1, len(jobs)) or a literal pool large enough for a literal range')
        if (not isinstance(wait, ast.For) or wait.orelse or not isinstance(wait.target, ast.Name)
                or not isinstance(wait.iter, ast.Name) or wait.iter.id != submit.targets[0].id or len(wait.body) != 1):
            self.reject(wait, 'wait for every submitted future')
        expected = ast.parse(f'{wait.target.id}.result()').body[0]
        if ast.dump(wait.body[0], include_attributes=False) != ast.dump(expected, include_attributes=False):
            self.reject(wait, 'wait with future.result() so worker exceptions propagate')
        local_names = [item.optional_vars.id, submit.targets[0].id, wait.target.id]
        if (len(local_names) != len(set(local_names)) or any(n in self.locks + self.inputs + list(self.arrays) + [self.worker_arg] for n in local_names)):
            self.reject(statement, 'executor locals must not shadow trial inputs or allocations')
        return call, loop

    def expression(self, expression, env, heap=None):
        if isinstance(expression, ast.Name) and expression.id in env:
            return env[expression.id]
        integer = integer_literal(expression)
        if integer is not None:
            return Value(f'({integer} : Int)', 'int')
        if isinstance(expression, ast.Constant):
            if type(expression.value) is bool:
                return Value(str(expression.value).lower(), 'bool')
        if isinstance(expression, ast.Subscript) and not isinstance(expression.slice, ast.Slice) and heap is not None:
            array = self.expression(expression.value, env, heap)
            index = self.expression(expression.slice, env, heap)
            if array.kind != ('array', 'int') or index.kind != 'int':
                self.reject(expression, 'trial indexing currently needs an integer list and integer index')
            return Value(f'(← PyTrial.readIntItem {heap} ({array.code}) ({index.code}))', 'int')
        if isinstance(expression, ast.List):
            parts, kind = [], None
            for element in expression.elts:
                value = self.expression(element.value if isinstance(element, ast.Starred) else element, env, heap)
                if isinstance(element, ast.Starred):
                    if not isinstance(value.kind, tuple) or value.kind[0] != 'list':
                        self.reject(element, 'starred elements need a list')
                    element_kind, code = value.kind[1], value.code
                else:
                    element_kind, code = value.kind, f'[{value.code}]'
                if kind is not None and element_kind != kind:
                    self.reject(element, 'heterogeneous trial lists are currently unsupported')
                kind = element_kind
                parts.append(code)
            return Value('(' + (' ++ '.join(parts) or '([] : List Int)') + ')', ('list', kind or 'int'))
        if isinstance(expression, ast.Subscript) and isinstance(expression.slice, ast.Slice):
            value = self.expression(expression.value, env, heap)
            if not isinstance(value.kind, tuple) or value.kind[0] != 'list':
                self.reject(expression, 'slicing needs a list')
            part = expression.slice
            bounds = [part.lower, part.upper]
            if part.step is not None or any(n is not None and (not isinstance(n, ast.Constant) or type(n.value) is not int or n.value < 0) for n in bounds):
                self.reject(expression, 'trial slices currently use nonnegative literal bounds and unit step')
            start = part.lower.value if part.lower else 0
            code = f'({value.code}).drop {start}'
            if part.upper is not None:
                code = f'(({code}).take {max(0, part.upper.value - start)})'
            return Value(f'({code})', value.kind)
        if isinstance(expression, ast.Call) and isinstance(expression.func, ast.Name) and not expression.keywords:
            args = [self.expression(n, env, heap) for n in expression.args]
            if expression.func.id == 'range' and len(args) == 1 and args[0].kind == 'int':
                return Value(f'(List.range ({args[0].code}).toNat).map Int.ofNat', ('list', 'int'))
            if expression.func.id == 'zip' and len(args) == 2 and all(isinstance(v.kind, tuple) and v.kind[0] == 'list' for v in args):
                return Value(f'({args[0].code}).zip ({args[1].code})', ('list', ('pair', args[0].kind[1], args[1].kind[1])))
            if expression.func.id == 'len' and len(args) == 1 and isinstance(args[0].kind, tuple) and args[0].kind[0] == 'list':
                return Value(f'(({args[0].code}).length : Int)', 'int')
        if isinstance(expression, ast.Compare) and len(expression.ops) == 1:
            left = self.expression(expression.left, env, heap)
            right = self.expression(expression.comparators[0], env, heap)
            op = expression.ops[0]
            if isinstance(op, (ast.Eq, ast.NotEq)) and left.kind == right.kind:
                return Value(f'({left.code}) {"!=" if isinstance(op, ast.NotEq) else "=="} ({right.code})', 'bool')
        self.reject(expression, f'unsupported trial expression: {ast.unparse(expression)}')


    def lean_type(self, kind):
        if isinstance(kind, tuple) and kind[0] == 'pair':
            return f'({self.lean_type(kind[1])} × {self.lean_type(kind[2])})'
        if isinstance(kind, tuple) and kind[0] == 'list':
            return f'List ({self.lean_type(kind[1])})'
        return {'int': 'Int', 'bool': 'Bool'}[kind]

    def bind(self, target, value, env, *, new=False):
        if isinstance(target, ast.Name):
            if new and target.id in env:
                self.reject(target, 'loop variables must not shadow earlier trial variables')
            env[target.id] = value
        elif isinstance(target, ast.Tuple) and len(target.elts) == 2 and isinstance(value.kind, tuple) and value.kind[0] == 'pair':
            self.bind(target.elts[0], Value(f'({value.code}).1', value.kind[1]), env, new=new)
            self.bind(target.elts[1], Value(f'({value.code}).2', value.kind[2]), env, new=new)
        else:
            self.reject(target, 'unsupported assignment target or tuple unpacking')

    def compile_setup(self, statements, env, heap, allocated, nested=False):
        for statement in statements:
            if id(statement) in self.allocations:
                if nested:
                    self.reject(statement, 'allocate lists and locks before setup loops')
                for name, _ in self.allocations[id(statement)]:
                    if name in env:
                        self.reject(statement, f'reassigned allocation name {name!r}')
                    env[name] = allocated[name]
            elif isinstance(statement, ast.Assign) and len(statement.targets) == 1:
                target = statement.targets[0]
                if not nested:
                    if any(isinstance(n, ast.Name) and n.id in self.inputs + [self.worker_arg] for n in ast.walk(target)):
                        self.reject(target, 'trial inputs cannot be rebound during setup')
                    self.bind(target, self.expression(statement.value, env), env)
                else:
                    self.reject(statement, 'setup-loop locals currently come from its iteration variables')
            elif isinstance(statement, ast.For) and not statement.orelse:
                iterable = self.expression(statement.iter, env)
                if not isinstance(iterable.kind, tuple) or iterable.kind[0] != 'list':
                    self.reject(statement, 'for loops need lists or zip')
                state, item = self.fresh('heap'), self.fresh('item')
                inner = env.copy()
                self.bind(statement.target, Value(item, iterable.kind[1]), inner, new=True)
                updated = self.compile_setup(statement.body, inner, state, allocated, nested=True)
                heap = f'({iterable.code}).foldl (fun {state} ({item} : {self.lean_type(iterable.kind[1])}) => {updated}) ({heap})'
            else:
                self.reject(statement, f'unsupported trial setup statement: {ast.unparse(statement)}')
        return heap

    def compile_post(self, statements, env, result='()', heap=None):
        if heap is None:
            heap = self.final_name
        lines = []
        for statement in statements:
            if isinstance(statement, ast.Assign) and len(statement.targets) == 1 and isinstance(statement.targets[0], ast.Name):
                name = statement.targets[0].id
                value = self.expression(statement.value, env, heap)
                local = self.fresh('local')
                lines.append(f'let {local} := {value.code};')
                env[name] = Value(local, value.kind)
            elif isinstance(statement, ast.Assert):
                self.check_message(statement.msg, env, heap)
                value = self.expression(statement.test, env, heap)
                if value.kind != 'bool':
                    self.reject(statement, 'assert needs a supported Boolean expression')
                lines.append(f'PyTrial.assertTrue ({value.code});')
            elif isinstance(statement, ast.For) and not statement.orelse:
                iterable = self.expression(statement.iter, env, heap)
                if not isinstance(iterable.kind, tuple) or iterable.kind[0] != 'list':
                    self.reject(statement, 'assertion loops need lists or zip')
                assigned = {n.targets[0].id for s in statement.body for n in ast.walk(s)
                            if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name)}
                carried = sorted(assigned.intersection(env))
                if carried:
                    self.reject(statement, 'loop-carried trial locals are unsupported')
                state, item = self.fresh('state'), self.fresh('item')
                inner = env.copy()
                self.bind(statement.target, Value(item, iterable.kind[1]), inner, new=True)
                body = self.compile_post(statement.body, inner, heap=heap)
                loop_result = self.fresh('result')
                lines.append(f'let {loop_result} ← ({iterable.code}).foldlM (fun {state} ({item} : {self.lean_type(iterable.kind[1])}) => do {body}) ();')
            else:
                self.reject(statement, f'unsupported trial assertion statement: {ast.unparse(statement)}')
        if result is not None:
            lines.append(f'pure {result}')
        return ' '.join(lines)

    def check_message(self, message, env, heap):
        """Messages do not affect success, but their Python must be supported."""
        if message is None or isinstance(message, ast.Constant) and isinstance(message.value, str):
            return
        if isinstance(message, ast.JoinedStr):
            for part in message.values:
                if isinstance(part, ast.Constant) and isinstance(part.value, str):
                    continue
                if (isinstance(part, ast.FormattedValue) and part.conversion == -1 and part.format_spec is None
                        and self.expression(part.value, env, heap).kind in ('int', 'bool')):
                    continue
                self.reject(part, 'assert f-strings support plain integer and Boolean interpolations')
            return
        self.reject(message, 'assert messages need string literals or supported scalar f-strings')

    def worker(self, env):
        iterable = self.expression(self.loop.iter, env)
        if iterable.kind != ('list', 'int'):
            self.reject(self.loop, 'workers currently iterate over an integer range or list')
        inner = env.copy()
        self.bind(self.loop.target, Value(self.job_name, iterable.kind[1]), inner, new=True)
        args = self.function.args.args
        if len(args) != len(self.call.args) - 1:
            self.reject(self.call, 'submitted argument count does not match the worker')
        arguments = []
        for parameter, expression in zip(args, self.call.args[1:]):
            value = self.expression(expression, inner)
            if value.kind == 'lock':
                if not isinstance(parameter.annotation, ast.Name) or parameter.annotation.id != 'Lock':
                    self.reject(expression, 'Lock arguments must match annotations')
                arguments.append(f'.lock {value.code}')
            elif (value.kind == ('array', 'int') and isinstance(parameter.annotation, ast.Subscript)
                    and isinstance(parameter.annotation.value, ast.Name) and parameter.annotation.value.id == 'list'
                    and isinstance(parameter.annotation.slice, ast.Name) and parameter.annotation.slice.id == 'int'):
                arguments.append(f'.ref ({value.code})')
            elif value.kind in ('int', 'bool') and isinstance(parameter.annotation, ast.Name) and parameter.annotation.id == value.kind:
                arguments.append(f'.{value.kind} ({value.code})')
            else:
                self.reject(expression, 'submitted arguments must match worker parameter annotations')
        return iterable.code, arguments

    def unsupported(self):
        issues = []
        for statement in body_of(self.function):
            # Lock operations may occur inside supported branches and loops.
            lock_calls = {id(node.func) for node in ast.walk(statement)
                          if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                          and node.func.attr in {'acquire', 'release'} and not node.args and not node.keywords}
            for node in ast.walk(statement):
                if (isinstance(node, ast.Attribute) and id(node) not in lock_calls):
                    issues.append((node.lineno, f'quoted workers cannot access reference field {node.attr!r}'))
        return issues
