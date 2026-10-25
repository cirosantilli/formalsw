"""Validate unbounded standard-library cache decorators without executing them."""
import ast
from pathlib import Path

from lang.py.imports import bindings
from lang.py.call_graph import call_targets


def cache_decorator(module, function):
    """Recognize only an unmodified functools.lru_cache(None) binding."""
    if len(function.decorator_list) != 1:
        return False
    decorator = function.decorator_list[0]
    if not isinstance(decorator, ast.Call):
        return False
    positional = (len(decorator.args) == 1 and not decorator.keywords
                  and isinstance(decorator.args[0], ast.Constant) and decorator.args[0].value is None)
    keyword = (not decorator.args and len(decorator.keywords) == 1
               and decorator.keywords[0].arg == 'maxsize'
               and isinstance(decorator.keywords[0].value, ast.Constant)
               and decorator.keywords[0].value.value is None)
    if not (positional or keyword):
        return False
    target = decorator.func
    name = target.id if isinstance(target, ast.Name) else (
        target.value.id if isinstance(target, ast.Attribute) and isinstance(target.value, ast.Name)
        and target.attr == 'lru_cache' else None)
    if name is None:
        return False
    imports = bindings(module, name)
    if len(imports) != 1 or imports[0] not in module.body:
        return False
    imported = imports[0]
    if isinstance(target, ast.Name):
        if not (isinstance(imported, ast.ImportFrom) and imported.module == 'functools'
                and imported.level == 0 and any(alias.name == 'lru_cache'
                    and (alias.asname or alias.name) == name for alias in imported.names)):
            return False
    elif not (isinstance(imported, ast.Import) and any(alias.name == 'functools'
                and (alias.asname or alias.name) == name for alias in imported.names)):
        return False
    aliases = {alias.asname or alias.name for node in module.body if isinstance(node, ast.Import)
               for alias in node.names if alias.name == 'functools'}
    if any(isinstance(node, ast.Attribute) and isinstance(node.ctx, (ast.Store, ast.Del))
           and isinstance(node.value, ast.Name) and node.value.id in aliases for node in ast.walk(module)):
        return False
    direct = {alias.asname or alias.name for node in module.body
              if isinstance(node, ast.ImportFrom) and node.module == 'functools' and node.level == 0
              for alias in node.names if alias.name == 'lru_cache'}
    allowed = set()
    for node in module.body:
        if isinstance(node, ast.FunctionDef):
            for item in node.decorator_list:
                if isinstance(item, ast.Call):
                    func = item.func
                    if (isinstance(func, ast.Name) and func.id in direct
                            or isinstance(func, ast.Attribute) and func.attr == 'lru_cache'
                            and isinstance(func.value, ast.Name) and func.value.id in aliases):
                        allowed.update(id(part) for part in ast.walk(func))
    if any(isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)
           and node.id in aliases | direct and id(node) not in allowed for node in ast.walk(module)):
        # Escaping aliases could mutate the shared module or decorator through
        # setattr or another helper before the source function is defined.
        return False
    source = getattr(module, 'formalsw_source', None)
    roots = (Path(source).parent, Path.cwd()) if source is not None else (Path.cwd(),)
    if any((root / 'functools.py').exists() or (root / 'functools').is_dir() for root in roots):
        return False
    return True


def memoized_names(module):
    return [node.name for node in module.body if isinstance(node, ast.FunctionDef)
            and cache_decorator(module, node)]


def uses_memoized(module, function):
    """Follow ordinary calls and named callbacks, including mutual recursion."""
    functions = {node.name: node for node in module.body if isinstance(node, ast.FunctionDef)}
    pending, seen = [function], set()
    while pending:
        current = pending.pop()
        if current.name in seen:
            continue
        seen.add(current.name)
        if cache_decorator(module, current):
            return True
        for node in (part for statement in current.body for part in ast.walk(statement)):
            pending.extend(functions[target] for target in call_targets(node) if target in functions)
    return False
