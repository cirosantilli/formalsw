"""
Identify tuple wrappers whose identities cannot escape immediate unpacking.
"""
import ast


def flat_unpacking(target):
    """Recognize tuple/list targets containing only ordinary local names."""
    return (isinstance(target, (ast.Tuple, ast.List))
            and all(isinstance(item, ast.Name) for item in target.elts))


def unpacked_return_tuple_displays(module, entry):
    """
    Hide returned tuple wrappers only when every reachable use immediately
    unpacks them. The entry function's own return remains observable. This is
    deliberately conservative about forwarding, aliases, and discarded calls;
    none of those qualify as an unpacking use.
    """
    functions = {node.name: node for node in module.body if isinstance(node, ast.FunctionDef)}
    reachable = set()
    pending = [entry]
    calls = {}
    while pending:
        function = pending.pop()
        if function in reachable:
            continue
        reachable.add(function)
        parts = list(ast.walk(function))
        parents = {child: parent for parent in parts for child in ast.iter_child_nodes(parent)}
        for node in parts:
            if not isinstance(node, ast.Name) or not isinstance(node.ctx, ast.Load) or node.id not in functions:
                continue
            callee = functions[node.id]
            parent = parents.get(node)
            assignment = parents.get(parent)
            consumed = (isinstance(parent, ast.Call) and parent.func is node
                        and isinstance(assignment, ast.Assign) and assignment.value is parent
                        and len(assignment.targets) == 1 and flat_unpacking(assignment.targets[0]))
            calls.setdefault(callee, []).append(consumed)
            pending.append(callee)
    hidden = set()
    for function, uses in calls.items():
        if function is entry or not all(uses):
            continue
        for node in ast.walk(function):
            if isinstance(node, ast.Return) and isinstance(node.value, ast.Tuple):
                hidden.add(node.value)
    return hidden


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
    immediate = set()
    def unpacked_branches(value):
        if isinstance(value, ast.Tuple):
            immediate.add(value)
        elif isinstance(value, ast.IfExp):
            unpacked_branches(value.body)
            unpacked_branches(value.orelse)
    for node in parts:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and flat_unpacking(node.targets[0]):
            unpacked_branches(node.value)
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
    return immediate | {item for table in tables for item in table.elts if isinstance(item, ast.Tuple)}
