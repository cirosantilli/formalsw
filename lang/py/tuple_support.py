"""
Identify tuple wrappers whose identities cannot escape immediate unpacking.
"""
import ast


def flat_unpacking(target):
    """Recognize tuple/list targets containing only ordinary local names."""
    return (isinstance(target, (ast.Tuple, ast.List))
            and all(isinstance(item, ast.Name) for item in target.elts))


def unpacked_tuple_displays(function):
    """
    Allow hidden tuple wrappers in inline iteration tables and local tables used
    exclusively by unpacking loops. Python may pool constant tuples; these uses
    expose only their elements, so fresh model wrappers have the same observable
    result. Aliasing, mutation, return, and every other use of a table reject it.
    """
    parts = list(ast.walk(function))
    parents = {child: parent for parent in parts for child in ast.iter_child_nodes(parent)}
    tables = set()
    for node in parts:
        if isinstance(node, (ast.For, ast.comprehension)) and flat_unpacking(node.target) and isinstance(node.iter, ast.List):
            tables.add(node.iter)
        if (isinstance(node, ast.Assign) and len(node.targets) == 1
                and isinstance(node.targets[0], ast.Name)):
            target, value = node.targets[0], node.value
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
            target, value = node.target, node.value
        else:
            continue
        if not isinstance(value, ast.List):
            continue
        if target.id in {arg.arg for arg in function.args.args}:
            continue
        occurrences = [part for part in parts if isinstance(part, ast.Name) and part.id == target.id]
        if all(part is target or isinstance(part.ctx, ast.Load)
               and isinstance(parents.get(part), (ast.For, ast.comprehension))
               and parents[part].iter is part and flat_unpacking(parents[part].target)
               for part in occurrences):
            tables.add(value)
    return {item for table in tables for item in table.elts if isinstance(item, ast.Tuple)}
