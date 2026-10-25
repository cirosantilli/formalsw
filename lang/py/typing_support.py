"""Resolve standard typing container aliases without importing user modules."""
import ast
from pathlib import Path

from lang.py.imports import bindings


def resolve_typing_annotations(module):
    """Attach validated domains while preserving the source annotation syntax.

    Only module-level signatures and globals use this resolver. Class and local
    annotation scopes need their own binding analysis before they can opt in.
    """
    for node in ast.walk(module):
        if hasattr(node, 'formalsw_typing_container'):
            del node.formalsw_typing_container
    source = getattr(module, 'formalsw_source', None)
    roots = (Path(source).parent, Path.cwd()) if source is not None else (Path.cwd(),)
    if any((root / 'typing.py').exists() or (root / 'typing').is_dir() for root in roots):
        return
    containers = {'List': 'list', 'Dict': 'dict', 'Set': 'set'}
    direct, qualified = {}, set()
    for statement in module.body:
        if isinstance(statement, ast.ImportFrom) and statement.module == 'typing' and statement.level == 0:
            for alias in statement.names:
                name = alias.asname or alias.name
                if alias.name in containers and bindings(module, name) == [statement]:
                    direct[name] = containers[alias.name]
        elif isinstance(statement, ast.Import):
            for alias in statement.names:
                name = alias.asname or alias.name
                if alias.name == 'typing' and bindings(module, name) == [statement]:
                    qualified.add(name)

    annotations = []
    for statement in module.body:
        if isinstance(statement, (ast.FunctionDef, ast.AsyncFunctionDef)):
            args = statement.args
            annotations.extend(arg.annotation for arg in (*args.posonlyargs, *args.args, *args.kwonlyargs))
            annotations.extend(arg.annotation for arg in (args.vararg, args.kwarg) if arg is not None)
            annotations.append(statement.returns)
        elif isinstance(statement, ast.AnnAssign):
            annotations.append(statement.annotation)
    allowed = {id(node) for annotation in annotations if annotation is not None for node in ast.walk(annotation)}
    # Function-local variable annotations are not evaluated by Python. They do
    # not resolve input domains, but using an alias there does not escape it.
    def local_annotations(node):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)):
            return
        if isinstance(node, ast.AnnAssign):
            allowed.update(id(part) for part in ast.walk(node.annotation))
        for child in ast.iter_child_nodes(node):
            local_annotations(child)

    for statement in module.body:
        if isinstance(statement, (ast.FunctionDef, ast.AsyncFunctionDef)):
            for node in statement.body:
                local_annotations(node)
    # An escaped module or alias could be modified through setattr or a helper.
    # Reject it conservatively even if the escape appears after the annotation.
    escaped = {node.id for node in ast.walk(module) if isinstance(node, ast.Name)
               and isinstance(node.ctx, ast.Load) and node.id in direct.keys() | qualified
               and id(node) not in allowed}
    for name in escaped:
        direct.pop(name, None)
        qualified.discard(name)
    if any(isinstance(node, ast.Attribute) and isinstance(node.ctx, (ast.Store, ast.Del))
           and isinstance(node.value, ast.Name) and node.value.id in qualified for node in ast.walk(module)):
        qualified.clear()
    for annotation in annotations:
        if annotation is None:
            continue
        for node in ast.walk(annotation):
            if isinstance(node, ast.Name) and node.id in direct:
                node.formalsw_typing_container = direct[node.id]
            elif (isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name)
                  and node.value.id in qualified and node.attr in containers):
                node.formalsw_typing_container = containers[node.attr]
