"""
Translate a deliberately small Nagini annotation dialect to executable Python AST.

This is a source-language convention, NOT equivalence to CPython executing the
contract library: ghost arguments (including calls, lambdas and exceptions) are
syntax and never evaluated. Canonical absolute imports declare annotation names;
we do not import or execute nagini_contracts. Only leading Requires, Ensures and
Decreases statements in module-level functions, and bare @Pure, are supported.
No Ghost functions, aliases, wildcard imports, nested contracts or runtime uses
of annotation names are accepted. Binding checks are deliberately scope-wide.

Imports referenced only by erased syntax are ghost dependencies, so their module
initialization is also outside the translated program. All other imports and
runtime syntax remain intact. The caller retains the ORIGINAL source snapshot;
this pass must run on fresh parsed source before linking, never on cached JSON.
"""

import ast
from hashlib import sha256

from lang.py.contracts import ContractError


CONTRACTS = {'Requires', 'Ensures', 'Decreases'}
IMPORTS = {
    'nagini_contracts.contracts': CONTRACTS | {'Pure', 'Old', 'Result'},
    'nagini_contracts.obligations': {'MustTerminate'},
}


def erase_nagini_annotations(module):
    """Validate first, then erase explicitly recognized non-evaluating syntax."""
    declarations = []
    names = set()
    declared_at = {}
    for node in ast.walk(module):
        aliases = node.names if isinstance(node, (ast.Import, ast.ImportFrom)) else []
        nagini = (isinstance(node, ast.ImportFrom)
                  and (node.module or '').split('.')[0] == 'nagini_contracts') or (
                      isinstance(node, ast.Import)
                      and any(alias.name.split('.')[0] == 'nagini_contracts' for alias in aliases))
        if not nagini:
            continue
        if (not isinstance(node, ast.ImportFrom) or node not in module.body
                or node.level or node.module not in IMPORTS):
            raise ContractError('Nagini erasure requires canonical absolute module-level from imports')
        for alias in aliases:
            if alias.asname is not None or alias.name not in IMPORTS[node.module] or alias.name in names:
                raise ContractError('Nagini erasure rejects aliases, duplicates and unsupported annotation imports')
            names.add(alias.name)
            declared_at[alias.name] = node.lineno
        declarations.append(node)
    if not declarations:
        return

    # Include binding forms that do not use ast.Name(Store), and reject shadowing
    # even in dead branches or unrelated lexical scopes rather than guessing.
    for node in ast.walk(module):
        bound = set()
        if isinstance(node, ast.Name) and node.id in names and node.lineno < declared_at[node.id]:
            raise ContractError('Nagini annotation used before its canonical import: ' + node.id)
        if isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)):
            bound.add(node.id)
        elif isinstance(node, ast.arg):
            bound.add(node.arg)
        elif type(node).__name__ in {'TypeVar', 'ParamSpec', 'TypeVarTuple'}:
            bound.add(node.name)
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            bound.add(node.name)
        elif isinstance(node, (ast.Import, ast.ImportFrom)) and node not in declarations:
            if any(alias.name == '*' for alias in node.names):
                raise ContractError('Nagini erasure rejects wildcard imports')
            bound.update(alias.asname or alias.name.split('.')[0] for alias in node.names)
        elif isinstance(node, (ast.Global, ast.Nonlocal)):
            bound.update(node.names)
        elif isinstance(node, ast.ExceptHandler) and node.name:
            bound.add(node.name)
        elif isinstance(node, (ast.MatchAs, ast.MatchStar)) and node.name:
            bound.add(node.name)
        elif isinstance(node, ast.MatchMapping) and node.rest:
            bound.add(node.rest)
        if bound & names:
            raise ContractError('Nagini annotation binding is rebound or shadowed: ' + ', '.join(sorted(bound & names)))

    erased = set(declarations)
    for function in module.body:
        if not isinstance(function, ast.FunctionDef):
            continue
        for decorator in function.decorator_list:
            if isinstance(decorator, ast.Name) and decorator.id == 'Pure' and 'Pure' in names:
                erased.add(decorator)
        prefix = True
        for index, statement in enumerate(function.body):
            if index == 0 and isinstance(statement, ast.Expr) and isinstance(statement.value, ast.Constant) and isinstance(statement.value.value, str):
                continue
            if (prefix and isinstance(statement, ast.Expr) and isinstance(statement.value, ast.Call)
                    and isinstance(statement.value.func, ast.Name)
                    and statement.value.func.id in CONTRACTS & names):
                call = statement.value
                arities = {'Requires': {1}, 'Ensures': {1, 2}, 'Decreases': {1, 2}}
                if len(call.args) not in arities[call.func.id] or call.keywords or any(isinstance(arg, ast.Starred) for arg in call.args):
                    raise ContractError('Nagini contract statements require explicit positional ghost arguments')
                erased.add(statement)
            else:
                prefix = False

    ghost_names = {node.id for root in erased for node in ast.walk(root) if isinstance(node, ast.Name)}
    runtime_names = set()

    def check_runtime(node):
        if node in erased:
            return
        if isinstance(node, ast.Name):
            runtime_names.add(node.id)
            if node.id in names:
                raise ContractError('Nagini annotation name used outside supported ghost syntax: ' + node.id)
        for child in ast.iter_child_nodes(node):
            check_runtime(child)

    check_runtime(module)
    ghost_only = ghost_names - runtime_names - names
    removed_imports = []
    ghost_import_lines = set()
    body = []
    for node in module.body:
        if node in erased:
            continue
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            keep = []
            for alias in node.names:
                binding = alias.asname or alias.name.split('.')[0]
                if binding in ghost_only:
                    removed_imports.append((getattr(node, 'module', None), alias.name))
                    ghost_import_lines.add(node.lineno)
                else:
                    keep.append(alias)
            node.names = keep
            if not keep:
                erased.add(node)
                continue
        if isinstance(node, ast.FunctionDef):
            node.decorator_list = [decorator for decorator in node.decorator_list if decorator not in erased]
            node.body = [statement for statement in node.body if statement not in erased]
            if not node.body:
                node.body = [ast.copy_location(ast.Pass(), node)]
        body.append(node)
    module.body = body
    module.formalsw_nagini_erasure = {
        'dialect': 'canonical-leading-contracts-v1',
        'annotations': tuple(sorted(names)),
        'ghost_imports': tuple(removed_imports),
        'ghost_import_lines': tuple(sorted(ghost_import_lines)),
        'erased_lines': tuple(sorted({node.lineno for node in erased})),
    }
    original = getattr(module, 'formalsw_source_text', None)
    if original is not None:
        module.formalsw_nagini_erasure['source_sha256'] = sha256(original.encode('utf-8')).hexdigest()
