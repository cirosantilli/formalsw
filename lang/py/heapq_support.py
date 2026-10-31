"""Resolve the min-heap operations without accepting mutable or escaped imports."""
import ast
from pathlib import Path

from lang.py.imports import bindings


HEAPQ_FUNCTIONS = ('heapify', 'heappush', 'heappop')


def heapq_functions(module):
    """Retain both direct imports and qualified module aliases."""
    result = {}
    for statement in module.body:
        if isinstance(statement, ast.ImportFrom) and statement.level == 0 and statement.module == 'heapq':
            for alias in statement.names:
                if alias.name in HEAPQ_FUNCTIONS:
                    result[alias.asname or alias.name] = ('heapq', alias.name, statement)
        elif isinstance(statement, ast.Import):
            for alias in statement.names:
                if alias.name == 'heapq':
                    for name in HEAPQ_FUNCTIONS:
                        result[f'{alias.asname or alias.name}.{name}'] = ('heapq', name, statement)
    return result


def heapq_binding(node, module):
    """Return the operation only when all uses preserve its standard binding."""
    if not isinstance(node, ast.Call):
        return None
    target = node.func
    name = target.id if isinstance(target, ast.Name) else (
        f'{target.value.id}.{target.attr}' if isinstance(target, ast.Attribute)
        and isinstance(target.value, ast.Name) else None)
    functions = heapq_functions(module)
    if name not in functions:
        return None
    _, operation, statement = functions[name]
    binding_name = name.split('.')[0]
    if bindings(module, binding_name) != [statement]:
        return None
    if sum((alias.asname or alias.name.split('.')[0]) == binding_name
           for alias in statement.names) != 1:
        return None
    aliases = {alias.asname or alias.name for statement in module.body if isinstance(statement, ast.Import)
               for alias in statement.names if alias.name == 'heapq'}
    direct = {name for name in functions if '.' not in name}
    allowed = set()
    for call in ast.walk(module):
        if not isinstance(call, ast.Call):
            continue
        function = call.func
        if (isinstance(function, ast.Name) and function.id in direct
                or isinstance(function, ast.Attribute) and function.attr in HEAPQ_FUNCTIONS
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
    if any((root / 'heapq.py').exists() or (root / 'heapq').is_dir() for root in roots):
        return None
    return operation
