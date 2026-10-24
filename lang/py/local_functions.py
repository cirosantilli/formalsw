"""Lift direct local calls while retaining late-bound captures and heap aliases.

Only nonescaping, unconditionally defined functions are lowered. Anything outside
this subset stays in the source AST, where ordinary coverage checking rejects it.
"""
import ast
import copy
import symtable


def lower_local_functions(module):
    if getattr(module, 'formalsw_locals_lowered', False):
        return
    module.formalsw_locals_lowered = True
    postponed = any(isinstance(node, ast.ImportFrom) and node.module == '__future__'
                    and any(alias.name == 'annotations' for alias in node.names) for node in module.body)
    occupied = {node.id for node in ast.walk(module) if isinstance(node, ast.Name)}
    occupied.update(node.name for node in ast.walk(module)
                    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)))
    additions = []
    for outer in list(module.body):
        if not isinstance(outer, ast.FunctionDef):
            continue
        children = [node for node in outer.body if isinstance(node, ast.FunctionDef)]
        if not children:
            continue
        try:
            lifted, body = _lower(outer, children, postponed, occupied)
        except (ValueError, SyntaxError) as error:
            outer.formalsw_local_function_error = str(error)
            continue
        outer.body = body
        additions.extend(lifted)
    module.body.extend(additions)
    ast.fix_missing_locations(module)


def _lower(outer, children, postponed, occupied):
    def reject(message):
        raise ValueError('local functions: ' + message)

    names = {child.name for child in children}
    if len(names) != len(children):
        reject('definitions must have distinct names')
    forbidden = (ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda, ast.Global, ast.Nonlocal,
                 ast.Yield, ast.YieldFrom, ast.Await, ast.NamedExpr, ast.Delete)
    if any(isinstance(node, forbidden) for node in ast.walk(outer)):
        reject('unsupported scope mutation, suspension, or nested scope')
    if any(isinstance(node, ast.FunctionDef) and node is not outer and node not in children
           for node in ast.walk(outer)):
        reject('definitions must be directly in the enclosing function body')
    if names & {arg.arg for arg in outer.args.posonlyargs + outer.args.args + outer.args.kwonlyargs}:
        reject('function names must not shadow parameters')
    for child in children:
        if (child.decorator_list or child.args.defaults or child.args.kw_defaults
                or child.args.posonlyargs or child.args.kwonlyargs or child.args.vararg or child.args.kwarg
                or getattr(child, 'type_params', [])):
            reject('decorators, defaults, and non-positional parameters are unsupported')
        if not postponed and (child.returns is not None or any(arg.annotation for arg in child.args.args)):
            reject('annotated definitions require from __future__ import annotations')
        if '@formalsw' in (ast.get_docstring(child, clean=False) or ''):
            reject('put contracts on the enclosing function')
        if any(isinstance(node, ast.Name) and node.id in names for node in ast.walk(child)):
            reject('recursive or sibling local function references are unsupported')

    # Python's symbol table distinguishes capture cells from comprehension locals
    # and global names. Adding parameters preserves those lexical distinctions.
    table = next(scope for scope in symtable.symtable(ast.unparse(outer), '<local-functions>', 'exec').get_children()
                 if scope.get_type() == 'function' and scope.get_name() == outer.name)
    scopes = {scope.get_name(): scope for scope in table.get_children() if scope.get_type() == 'function'}
    captures = {child.name: scopes[child.name].get_frees() for child in children}
    available = {arg.arg for arg in outer.args.posonlyargs + outer.args.args + outer.args.kwonlyargs}
    defined = set()
    for statement in outer.body:
        if statement in children:
            if not set(captures[statement.name]) <= available:
                reject('captures must be initialized before the local definition')
            defined.add(statement.name)
            continue
        calls = {id(node.func): node for node in ast.walk(statement)
                 if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)}
        for node in ast.walk(statement):
            if isinstance(node, ast.Name) and node.id in names:
                call = calls.get(id(node))
                if not isinstance(node.ctx, ast.Load) or call is None:
                    reject('local function values must not escape or be rebound')
                if node.id not in defined:
                    reject('calls must follow the local definition')
                if call.keywords:
                    reject('local calls require positional arguments')
        if isinstance(statement, ast.Assign):
            available.update(target.id for target in statement.targets if isinstance(target, ast.Name))
        elif isinstance(statement, ast.AnnAssign) and statement.value is not None and isinstance(statement.target, ast.Name):
            available.add(statement.target.id)

    replacements = {}
    lifted = []
    for child in children:
        fresh = f'__formalsw_local_{outer.name}_{child.name}'
        while fresh in occupied:
            fresh += '_'
        occupied.add(fresh)
        replacements[child.name] = fresh
        function = copy.deepcopy(child)
        function.name = fresh
        function.formalsw_markers = []
        function.formalsw_imported = True
        for name in captures[child.name]:
            argument = ast.arg(arg=name, annotation=None)
            argument.formalsw_capture = True
            function.args.args.append(ast.copy_location(argument, child))
        lifted.append(function)

    class Calls(ast.NodeTransformer):
        def visit_Call(self, node):
            self.generic_visit(node)
            if isinstance(node.func, ast.Name) and node.func.id in replacements:
                original = node.func.id
                node.func.id = replacements[original]
                node.args.extend(ast.copy_location(ast.Name(id=name, ctx=ast.Load()), node)
                                 for name in captures[original])
            return node

    body = [Calls().visit(copy.deepcopy(statement)) for statement in outer.body if statement not in children]
    return lifted, body
