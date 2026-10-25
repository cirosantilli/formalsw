"""Recognize fresh iterators from unmodified standard-library imports."""
import ast
from pathlib import Path

from lang.py.imports import bindings


def permutation_binding(node, module):
    """Find a stable imported constructor, rejecting shadowing and escaped aliases."""
    if not isinstance(node, ast.Call):
        return None
    target = node.func
    name = target.id if isinstance(target, ast.Name) else (
        target.value.id if isinstance(target, ast.Attribute) and target.attr == 'permutations'
        and isinstance(target.value, ast.Name) else None)
    if name is None:
        return None
    imported = bindings(module, name)
    if len(imported) != 1 or imported[0] not in module.body:
        return None
    binding = imported[0]
    if isinstance(target, ast.Name):
        if not (isinstance(binding, ast.ImportFrom) and binding.module == 'itertools'
                and binding.level == 0 and any(alias.name == 'permutations'
                    and (alias.asname or alias.name) == name for alias in binding.names)):
            return None
    elif not (isinstance(binding, ast.Import) and any(alias.name == 'itertools'
              and (alias.asname or alias.name) == name for alias in binding.names)):
        return None
    aliases = {alias.asname or alias.name for statement in module.body if isinstance(statement, ast.Import)
               for alias in statement.names if alias.name == 'itertools'}
    direct = {alias.asname or alias.name for statement in module.body
              if isinstance(statement, ast.ImportFrom) and statement.module == 'itertools' and statement.level == 0
              for alias in statement.names if alias.name == 'permutations'}
    allowed = set()
    for call in ast.walk(module):
        if isinstance(call, ast.Call):
            function = call.func
            if (isinstance(function, ast.Name) and function.id in direct
                    or isinstance(function, ast.Attribute) and function.attr == 'permutations'
                    and isinstance(function.value, ast.Name) and function.value.id in aliases):
                allowed.update(id(part) for part in ast.walk(function))
    if any(isinstance(part, ast.Name) and part.id in aliases | direct
           and isinstance(part.ctx, ast.Load) and id(part) not in allowed for part in ast.walk(module)):
        return None
    if any(isinstance(part, ast.Attribute) and isinstance(part.ctx, (ast.Store, ast.Del))
           and isinstance(part.value, ast.Name) and part.value.id in aliases for part in ast.walk(module)):
        return None
    source = getattr(module, 'formalsw_source', None)
    roots = (Path(source).parent, Path.cwd()) if source is not None else (Path.cwd(),)
    if any((root / 'itertools.py').exists() or (root / 'itertools').is_dir() for root in roots):
        return None
    return name


def permutation_arguments(node, module):
    """One positional pool and an optional positional or keyword length."""
    if permutation_binding(node, module) is None:
        return None
    if len(node.args) == 1 and not node.keywords:
        return [node.args[0], ast.Constant(value=None)]
    if len(node.args) == 2 and not node.keywords:
        return node.args
    if len(node.args) == 1 and len(node.keywords) == 1 and node.keywords[0].arg == 'r':
        return [node.args[0], node.keywords[0].value]
    return None
