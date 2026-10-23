"""Link explicit local helper imports while preserving their source definitions."""
import ast
from copy import deepcopy
import sys

from lang.py.contracts import ContractError
from lang.py.imports import resolve_function


def imported_calls(module):
    imports = {alias.asname or alias.name: node
               for node in module.body if isinstance(node, ast.ImportFrom)
               and (node.level or (node.module or '').split('.')[0] not in sys.stdlib_module_names)
               for alias in node.names if alias.name != '*'}
    calls = {node.func.id for function in module.body if isinstance(function, ast.FunctionDef)
             for node in ast.walk(function) if isinstance(node, ast.Call)
             and isinstance(node.func, ast.Name)}
    return sorted(calls & imports.keys())


def scope_names(module):
    """Conservative module binding names, including conditional writes."""
    result = set()
    def visit(node):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            result.add(node.name)
            return
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            if isinstance(node, ast.ImportFrom) and node.module == '__future__':
                return
            result.update(alias.asname or alias.name.split('.')[0] for alias in node.names)
            return
        if isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)):
            result.add(node.id)
        for child in ast.iter_child_nodes(node):
            visit(child)
    visit(module)
    return result


def free_calls(module):
    """Names resolved outside this module must not capture linked declarations."""
    return {node.func.id for node in ast.walk(module)
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)} - scope_names(module)


def link_imports(source, module, load):
    """
    Append complete helper modules so existing execution proofs can be transported
    with Calls.Extends. Reject collisions instead of changing lexical resolution.
    Imported declarations retain their bodies; aliases use small call wrappers.
    """
    selections = []
    for name in imported_calls(module):
        path, _, function = resolve_function(source, module, name)
        selections.append((name, path, function.name))
    for name, (path, captured, function) in getattr(module, 'formalsw_predicate_references', ()):
        if path.read_text() != captured.formalsw_source_text:
            raise ContractError(f'{path}: source changed after specification loading; rerun the checker')
        selections.append((name, path, function.name))
    module.formalsw_link_dependencies = tuple(dict.fromkeys(path for _, path, _ in selections))
    if not selections:
        return
    selected = {name for name, _, _ in selections}
    prefix = []
    for node in module.body:
        if isinstance(node, ast.ImportFrom):
            aliases = [alias for alias in node.names if (alias.asname or alias.name) not in selected]
            if len(aliases) != len(node.names):
                if aliases:
                    node = deepcopy(node)
                    node.names = aliases
                else:
                    continue
        prefix.append(node)
    linked = ast.Module(body=list(prefix), type_ignores=[])
    occupied = scope_names(linked)
    free = free_calls(linked) - selected
    aliases = []
    for path in module.formalsw_link_dependencies:
        dependency = load(path)
        names = scope_names(dependency)
        dependency_free = free_calls(dependency)
        collisions = (names & occupied) | (names & free) | (dependency_free & occupied)
        if collisions:
            raise ContractError(f'local helper imports have conflicting module bindings: {", ".join(sorted(collisions))}')
        # Check each selected function in its own module before flattening. A
        # missing helper must never accidentally resolve to a caller definition.
        from lang.py.support import SupportChecker
        coverage = SupportChecker(dependency)
        for alias, selected_path, target in selections:
            if selected_path != path:
                continue
            issues = coverage.check(target)
            if issues:
                raise ContractError(f'local helper {path}:{target} is unsupported: {issues[0].reason}')
            if alias != target:
                if alias in occupied or alias in names or alias in free or alias in dependency_free:
                    raise ContractError(f'local helper alias conflicts with a module binding: {alias}')
                function = next(node for node in dependency.body
                                if isinstance(node, ast.FunctionDef) and node.name == target)
                wrapper = ast.FunctionDef(name=alias, args=deepcopy(function.args),
                    body=[ast.Return(ast.Call(func=ast.Name(id=target, ctx=ast.Load()),
                        args=[ast.Name(id=arg.arg, ctx=ast.Load()) for arg in function.args.args], keywords=[]))],
                    decorator_list=[], returns=deepcopy(function.returns), type_params=[])
                ast.fix_missing_locations(wrapper)
                wrapper.formalsw_imported = True
                aliases.append(wrapper)
                occupied.add(alias)
        body = deepcopy(dependency.body)
        for node in body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                node.formalsw_imported = True
        linked.body.extend(body)
        occupied.update(names)
        free.update(dependency_free)
    # Put alias wrappers before dependency bodies to preserve a common suffix
    # for the first linked module's source proof.
    module.body = [*prefix, *aliases, *linked.body[len(prefix):]]
