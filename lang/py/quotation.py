"""Compile a single Python AST quotation; Lean owns syntax, scope and logic.

The JSON entry point is called by the native Lean elaborator. It returns a
closed lambda plus explicit captures, never rewrites a Lean theorem string.
"""
import ast
import json
from pathlib import Path
import symtable
import sys

from .concurrent_spec import Trial, Value, ScenarioError, ScenarioUnsupported, body_of, quoted, identifier, integer_literal


class Quotations:
    def __init__(self, module, function, namespace, captures):
        self.module, self.function, self.namespace = module, function, namespace
        self.captures = captures
        self.bound = set(captures) | set(captures.values())
        self.serial = 0
        self.stack = []
        self.functions = {node.name: node for node in module.body if isinstance(node, ast.FunctionDef)}

    def reject(self, node, message):
        raise ScenarioUnsupported(getattr(node, 'lineno', self.function.lineno), message)

    def fresh(self):
        self.serial += 1
        name = f'_quotation{self.serial}'
        while name in self.bound:
            name += '_'
        return name

    def global_name(self, name, expected=None):
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
        if bindings != ([] if expected is None else [expected]):
            self.reject(expected or self.function, f'py requires an unshadowed {name}')

    def expression(self, node, env):
        if isinstance(node, ast.Name) and node.id in env:
            return f'some ({env[node.id].code})'
        integer = integer_literal(node)
        if integer is not None:
            return f'some (PyValue.int ({integer}))'
        if isinstance(node, ast.Constant):
            if type(node.value) is bool:
                return f'some (PyValue.bool {str(node.value).lower()})'
            if type(node.value) is str:
                return f'some (PyValue.string {quoted(node.value)})'
            if node.value is None:
                return 'some PyValue.none'
        if isinstance(node, ast.List):
            elements = ', '.join(self.expression(n, env) for n in node.elts)
            return f'(((List.mapM id ([{elements}] : List (Option PyValue))) : Option (List PyValue)).map PyValue.list)'
        if isinstance(node, ast.BoolOp) and isinstance(node.op, ast.And):
            inner, terms = env.copy(), []
            for value in node.values:
                if self.kind(value, inner) != 'bool':
                    self.reject(value, 'quoted and operands currently require Boolean conditions')
                terms.append(self.expression(value, inner))
                self.refine(value, inner)
            result = terms[-1]
            for term in reversed(terms[:-1]):
                result = f'PyValue.andThen ({term}) (fun _ => {result})'
            return result
        if isinstance(node, ast.Compare) and len(node.ops) == 1:
            left, right = node.left, node.comparators[0]
            if (isinstance(left, ast.Call) and isinstance(left.func, ast.Name) and left.func.id == 'type'
                    and len(left.args) == 1 and not left.keywords and isinstance(right, ast.Name)
                    and right.id in ('int', 'list', 'bool', 'str') and isinstance(node.ops[0], (ast.Eq, ast.Is))):
                self.global_name('type'); self.global_name(right.id)
                if 'type' in env or right.id in env:
                    self.reject(node, 'Python type primitives cannot be shadowed by quotation locals')
                return f'({self.expression(left.args[0], env)}).bind (fun value => PyValue.typeIs value {quoted(right.id)})'
            ops = {ast.Eq: 'eq', ast.NotEq: 'notEq', ast.Lt: 'lt', ast.LtE: 'ltE', ast.Gt: 'gt', ast.GtE: 'gtE'}
            if type(node.ops[0]) in ops:
                if self.kind(left, env) != 'int' or self.kind(right, env) != 'int':
                    self.reject(node, 'quoted numeric comparisons need preceding Python type(... ) == int guards')
                lvar, rvar = self.fresh(), self.fresh()
                return f'(do let {lvar} ← {self.expression(left, env)}; let {rvar} ← {self.expression(right, env)}; PyValue.compare .{ops[type(node.ops[0])]} {lvar} {rvar})'
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and not node.keywords:
            name = node.func.id
            if name in env:
                self.reject(node, 'calling a Python value captured from Lean is not yet supported')
            if name == 'len' and len(node.args) == 1:
                self.global_name(name)
                if self.kind(node.args[0], env) not in ('list', 'str'):
                    self.reject(node, 'len in a quotation needs a preceding Python list or str type guard')
                return f'({self.expression(node.args[0], env)}).bind PyValue.length'
            if name == 'all' and len(node.args) == 1 and isinstance(node.args[0], ast.GeneratorExp):
                self.global_name(name)
                generator = node.args[0]
                if len(generator.generators) == 1:
                    loop = generator.generators[0]
                    if isinstance(loop.target, ast.Name) and not loop.ifs and not loop.is_async:
                        local = self.fresh()
                        if self.kind(loop.iter, env) != 'list':
                            self.reject(loop.iter, 'all in a quotation needs a preceding Python list type guard')
                        inner = dict(env, **{loop.target.id: Value(local, 'unknown')})
                        if self.kind(generator.elt, inner) != 'bool':
                            self.reject(generator.elt, 'all currently requires Boolean predicate results')
                        return (f'({self.expression(loop.iter, env)}).bind (PyValue.all '
                                f'(fun {local} => {self.expression(generator.elt, inner)}))')
            if name in self.functions:
                helper = self.functions[name]
                self.global_name(name, helper)
                if name in self.stack:
                    self.reject(helper, 'recursive predicate helpers are not yet supported')
                args = helper.args
                body = body_of(helper)
                if (helper.decorator_list or args.defaults or args.posonlyargs or args.kwonlyargs or args.vararg or args.kwarg
                        or len(args.args) != len(node.args) or len(body) != 1 or not isinstance(body[0], ast.Return)):
                    self.reject(helper, 'predicate helpers currently need positional parameters and one return expression')
                local_names = [self.fresh() for _ in node.args]
                lets = ' '.join(f'let {local} ← {self.expression(value, env)};' for local, value in zip(local_names, node.args))
                local_env = {arg.arg: Value(local, self.kind(value, env)) for arg, local, value in zip(args.args, local_names, node.args)}
                if self.kind(body[0].value, local_env) != 'bool':
                    self.reject(body[0], 'quoted predicate helpers must return a supported Boolean expression')
                self.stack.append(name)
                try:
                    result = self.expression(body[0].value, local_env)
                finally:
                    self.stack.pop()
                return f'(do {lets} {result})'
        self.reject(node, f'unsupported Python quotation expression: {ast.unparse(node)}')

    def kind(self, node, env):
        if integer_literal(node) is not None:
            return 'int'
        if isinstance(node, ast.Name) and node.id in env:
            return env[node.id].kind
        if isinstance(node, ast.Constant):
            return {int: 'int', bool: 'bool', str: 'str'}.get(type(node.value), 'unknown')
        if isinstance(node, ast.List):
            return 'list[int]' if all(self.kind(n, env) == 'int' for n in node.elts) else 'list'
        if isinstance(node, (ast.Compare, ast.BoolOp)):
            return 'bool'
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            if node.func.id == 'len':
                return 'int'
            if node.func.id == 'all' or node.func.id in self.functions:
                return 'bool'
        return 'unknown'

    def refine(self, node, env):
        if (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], (ast.Eq, ast.Is))
                and isinstance(node.left, ast.Call) and isinstance(node.left.func, ast.Name) and node.left.func.id == 'type'
                and len(node.left.args) == 1 and isinstance(node.left.args[0], ast.Name)
                and isinstance(node.comparators[0], ast.Name)):
            name, kind = node.left.args[0].id, node.comparators[0].id
            if name in env and kind in ('int', 'list', 'bool', 'str'):
                env[name] = Value(env[name].code, kind)

    def assumptions(self, node, env):
        refined = env.copy()
        if isinstance(node, ast.BoolOp) and isinstance(node.op, ast.And):
            for operand in node.values:
                refined = self.assumptions(operand, refined)
        elif (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
              and node.func.id in self.functions):
            helper = self.functions[node.func.id]
            arguments = helper.args.args
            inner = {arg.arg: Value(arg.arg, self.kind(value, env)) for arg, value in zip(arguments, node.args)}
            result = self.assumptions(body_of(helper)[0].value, inner)
            for arg, value in zip(arguments, node.args):
                if isinstance(value, ast.Name) and value.id in refined:
                    refined[value.id] = Value(refined[value.id].code, result[arg.arg].kind)
        elif (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'all'
              and len(node.args) == 1 and isinstance(node.args[0], ast.GeneratorExp)):
            generator = node.args[0]
            if len(generator.generators) == 1:
                loop = generator.generators[0]
                if isinstance(loop.target, ast.Name) and isinstance(loop.iter, ast.Name) and loop.iter.id in env:
                    inner = {loop.target.id: Value(loop.target.id, 'unknown')}
                    self.refine(generator.elt, inner)
                    if inner[loop.target.id].kind == 'int' and env[loop.iter.id].kind == 'list':
                        refined[loop.iter.id] = Value(env[loop.iter.id].code, 'list[int]')
        else:
            self.refine(node, refined)
        return refined

    def trial(self, node):
        if (not isinstance(node, ast.Call) or not isinstance(node.func, ast.Name) or node.keywords
                or not node.args or not isinstance(node.args[0], ast.Name) or node.args[0].id != 'this_function'):
            self.reject(node, 'quoted trial calls use helper(this_function, arguments...)')
        helper = self.functions.get(node.func.id)
        if helper is None:
            raise ScenarioError(f'unknown Python trial helper {node.func.id!r}')
        self.global_name(helper.name, helper)
        if len(helper.args.args) != len(node.args):
            self.reject(node, 'quoted trial argument count does not match the helper')
        env = {name: Value(code, 'unknown') for name, code in self.captures.items()}
        body = body_of(helper)
        if not body or not isinstance(body[0], ast.Assert):
            self.reject(helper, 'quoted trials need an initial assert establishing their Python input types')
        assertion = body[0]
        if assertion.msg is not None and not (isinstance(assertion.msg, ast.Constant) and type(assertion.msg.value) is str):
            self.reject(assertion, 'the input assertion message must be a string literal')
        local_names = [self.fresh() for _ in node.args[1:]]
        local_env = {arg.arg: Value(local, 'unknown') for arg, local in zip(helper.args.args[1:], local_names)}
        if self.kind(assertion.test, local_env) != 'bool':
            self.reject(assertion, 'the input assertion needs a Boolean condition')
        condition = self.expression(assertion.test, local_env)
        assumptions = self.assumptions(assertion.test, local_env)
        for parameter in helper.args.args[1:]:
            expected = ast.unparse(parameter.annotation) if parameter.annotation else ''
            if assumptions[parameter.arg].kind != expected:
                self.reject(parameter, f'the initial Python assertion must establish {expected or "a supported input type"} for {parameter.arg}')
        lets = ' '.join(f'let {local} ← {self.expression(value, env)};' for local, value in zip(local_names, node.args[1:]))
        condition = f'(do {lets} {condition})'
        arguments = {arg.arg: self.expression(value, env) for arg, value in zip(helper.args.args[1:], node.args[1:])}
        trial = QuotedTrial(helper.name, self.module, self.function, self.namespace, arguments=arguments, captured_names=self.bound)
        issues = trial.unsupported()
        if issues:
            line, message = issues[0]
            raise ScenarioUnsupported(line, message)
        return f'({{ condition := {condition}, body := {trial.execution()} }} : PyTrial.Call)'


class QuotedTrial(Trial):
    def __init__(self, *args, arguments, captured_names, **kwargs):
        self.arguments = arguments
        super().__init__(*args, **kwargs)
        self.setup = self.setup[1:]  # The leading assert is compiled by Quotations.trial.
        self.used_names.update(captured_names)
        self.job_name = self.unique('_job')
        self.final_name = self.unique('_final')
        for primitive in ('int', 'list'):
            if self.global_bindings(primitive):
                self.reject(self.helper, f'quoted trial annotations require an unshadowed {primitive}')
        if self.objects or self.collections:
            self.reject(self.helper, 'quoted trials currently support integer-list inputs and integer inputs; reference-object trials use Concurrent')

    def check_header(self):
        args = self.helper.args
        if self.helper.decorator_list or args.defaults or args.posonlyargs or args.kwonlyargs or args.vararg or args.kwarg or not args.args:
            self.reject(self.helper, 'quoted trials need ordinary positional parameters without defaults')
        self.worker_arg = args.args[0].arg
        self.inputs = []
        self.input_arrays = []
        for arg in args.args[1:]:
            annotation = ast.unparse(arg.annotation) if arg.annotation is not None else ''
            if annotation == 'int':
                self.inputs.append(arg.arg)
            elif annotation == 'list[int]':
                self.input_arrays.append(arg.arg)
                self.arrays[arg.arg] = None
            else:
                self.reject(arg, 'quoted trial parameters currently need Python int or list[int] annotations; the proof must justify these conversions')

    def expression(self, node, env, heap=None):
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == 'copy'
                and not node.args and not node.keywords and heap is None):
            value = super().expression(node.func.value, env)
            if value.kind == ('array', 'int'):
                return Value(self.array_contents[value.code], ('list', 'int'))
        if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub, ast.Mult)):
            left, right = self.expression(node.left, env, heap), self.expression(node.right, env, heap)
            if left.kind == right.kind == 'int':
                operator = {ast.Add: '+', ast.Sub: '-', ast.Mult: '*'}[type(node.op)]
                return Value(f'({left.code}) {operator} ({right.code})', 'int')
        if isinstance(node, ast.Subscript):
            value = self.expression(node.value, env, heap)
            if isinstance(node.slice, ast.Slice) and value.kind == ('array', 'int') and heap is not None:
                local = self.unique('_slice')
                inner = dict(env, **{local: Value(f'(← PyTrial.readInts {heap} ({value.code}))', ('list', 'int'))})
                return super().expression(ast.Subscript(value=ast.Name(id=local), slice=node.slice), inner, heap)
            if not isinstance(node.slice, ast.Slice) and value.kind == ('list', 'int'):
                index = self.expression(node.slice, env, heap)
                if index.kind == 'int':
                    return Value(f'(← PyTrial.intItem ({value.code}) ({index.code}))', 'int')
        return super().expression(node, env, heap)

    def execution(self):
        env, allocated, objects, prefix = {}, {}, [], []
        self.array_contents = {}
        for arg in self.helper.args.args[1:]:
            name = arg.arg
            raw, value = self.fresh('argument'), self.fresh('value')
            prefix.append(f'let {raw} ← {self.arguments[name]};')
            if name in self.input_arrays:
                prefix.append(f'let {value} ← {raw}.asInts;')
                address = str(len(objects))
                objects.append(f'.array ({value}.map SharedValue.int)')
                env[name] = Value(address, ('array', 'int'))
                self.array_contents[address] = value
            else:
                prefix.append(f'let {value} ← {raw}.asInt;')
                env[name] = Value(value, 'int')
        for statement in self.setup:
            for name, kind in self.allocations.get(id(statement), []):
                if kind == 'lock':
                    allocated[name] = Value(str(self.locks.index(name)), 'lock')
                elif kind == 'array':
                    address = str(len(objects))
                    values = '[' + ', '.join(f'({n} : Int)' for n in self.arrays[name]) + ']'
                    objects.append(f'.array ({values}.map SharedValue.int)')
                    allocated[name] = Value(address, ('array', 'int'))
                    self.array_contents[address] = values
                else:
                    self.reject(statement, 'unsupported allocation in quoted trial')
        env[self.worker_arg] = Value('_worker', 'callable')
        initial = f'({{ objects := [{", ".join(objects)}] }} : SharedState)'
        initial = self.compile_setup(self.setup, env, initial, allocated)
        jobs, _, _, _, arguments = self.worker(env)
        call = f'parallelFunction {self.namespace} {quoted(self.function.name)} [{", ".join(arguments)}]'
        if not any(self.job_name in value for value in arguments):
            calls = f'List.replicate ({jobs}).length ({call})'
        else:
            calls = f'({jobs}).map (fun {self.job_name} => {call})'
        post = self.compile_post(self.post, env.copy())
        return (f'((do {" ".join(prefix)} pure ({{ calls := {calls}, initial := {initial}, '
                f'check := fun {self.final_name} => do {post} }} : PyTrial)) : Option PyTrial)')



def free_names(expression):
    """Use Python's symbol table for lexical scope, including generators."""
    table = symtable.symtable(expression, '<py quotation>', 'eval')
    def globals_in(table):
        names = {symbol.get_name() for symbol in table.get_symbols()
                 if symbol.is_referenced() and symbol.is_global()}
        for child in table.get_children():
            names.update(globals_in(child))
        return names
    return globals_in(table)


def compile_quotation(module, function, expression, mode):
    # Parentheses allow a multiline expression without changing Python semantics.
    expression = '(' + expression + ')'
    try:
        node = ast.parse(expression, mode='eval').body
        names = free_names(expression)
    except SyntaxError as error:
        raise ScenarioError(f'invalid Python quotation: {error.msg}') from error
    functions = {n.name for n in module.body if isinstance(n, ast.FunctionDef)}
    captures = sorted(names - functions - {'type', 'len', 'all', 'int', 'list', 'bool', 'str', 'this_function'})
    module_name = '_python_module'
    while module_name in captures:
        module_name += '_'
    aliases = {name: f'_capture{index}' for index, name in enumerate(captures)}
    compiler = Quotations(module, function, identifier(module_name), aliases)
    if mode == 'condition':
        env = {name: Value(code, 'unknown') for name, code in aliases.items()}
        if compiler.kind(node, env) != 'bool':
            compiler.reject(node, 'a proposition quotation requires a supported Boolean expression')
        term = f'PyValue.IsTrue ({compiler.expression(node, env)})'
    elif mode in ('Returns', 'Throws'):
        term = f'PyTrial.Call.{mode} ({compiler.trial(node)})'
    else:
        compiler.reject(function, 'Halts for quoted concurrent trials is not yet supported; use Returns for successful termination')
    binders = ' '.join(f'({code} : PyValue)' for code in aliases.values())
    return {'captures': captures, 'term': f'fun ({identifier(module_name)} : Module) {binders} => {term}'}


def main():
    request = json.loads(sys.argv[1])
    try:
        source = Path(request['source'])
        module = ast.parse(source.read_text(), filename=str(source))
        function = next((n for n in module.body if isinstance(n, ast.FunctionDef) and n.name == request['function']), None)
        if function is None:
            raise ScenarioError(f"unknown enclosing Python function {request['function']!r}")
        from .support import SupportChecker
        issues = SupportChecker(module).requirement(function.name, 'theorem quotation : True')
        if issues:
            raise ScenarioUnsupported(issues[0].line, issues[0].reason)
        result = compile_quotation(module, function, request['expression'], request['mode'])
    except ScenarioUnsupported as error:
        result = {'unsupported': str(error), 'line': error.line}
    except (ScenarioError, OSError, SyntaxError) as error:
        result = {'error': str(error)}
    print(json.dumps(result))


if __name__ == '__main__':
    main()
