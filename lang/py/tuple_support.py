"""
Identify tuple wrappers whose identities cannot escape immediate unpacking.
"""
import ast


def flat_unpacking(target):
    """Recognize tuple/list targets containing only ordinary local names."""
    return (isinstance(target, (ast.Tuple, ast.List))
            and all(isinstance(item, ast.Name) for item in target.elts))


def runtime_tuple_element(node):
    """
    Recognize fields that prevent constant folding of a tuple display.

    Arithmetic and nested tuple construction evaluate their operands. Do not
    search arbitrary descendants: a conditional or short-circuit expression
    can discard a runtime name and fold to a constant.
    """
    if isinstance(node, (ast.Name, ast.Call, ast.List, ast.Attribute)):
        return True
    if isinstance(node, ast.Tuple):
        return any(runtime_tuple_element(item) for item in node.elts)
    if isinstance(node, ast.BinOp):
        return runtime_tuple_element(node.left) or runtime_tuple_element(node.right)
    if isinstance(node, ast.UnaryOp):
        return runtime_tuple_element(node.operand)
    if isinstance(node, ast.Subscript):
        return runtime_tuple_element(node.value) or runtime_tuple_element(node.slice)
    return False


def compared_set_tuple_displays(function):
    """
    A set display consumed directly by comparison cannot expose the identities
    of tuple constants it contains. Do not extend this through calls or other
    expressions that could retain a tuple or inspect its identity.
    """
    hidden = set()

    def tuple_elements(node):
        if isinstance(node, ast.Tuple):
            hidden.add(node)
            for item in node.elts:
                tuple_elements(item)

    for node in ast.walk(function):
        if not isinstance(node, ast.Compare):
            continue
        if not all(isinstance(op, (ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt, ast.GtE,
                                   ast.In, ast.NotIn)) for op in node.ops):
            continue
        for operand in (node.left, *node.comparators):
            if isinstance(operand, ast.Set):
                for item in operand.elts:
                    tuple_elements(item)
    return hidden


def compared_local_tuple_displays(module, function):
    """
    Hide flat scalar constants stored in locals used only by equality tests.

    A single binding and no aliases keep the wrapper private. Classes are
    excluded because a custom equality method could retain the compared tuple
    and observe its pooled identity on a later call.
    """
    if any(isinstance(node, ast.ClassDef) for node in ast.walk(module)):
        return set()
    parts = list(ast.walk(function))
    parents = {child: parent for parent in parts for child in ast.iter_child_nodes(parent)}
    parameters = {arg.arg for arg in ast.walk(function.args) if isinstance(arg, ast.arg)}
    hidden = set()
    for node in parts:
        if isinstance(node, ast.Assign) and len(node.targets) == 1:
            target, value = node.targets[0], node.value
        elif isinstance(node, ast.AnnAssign):
            target, value = node.target, node.value
        else:
            continue
        if not (isinstance(target, ast.Name) and target.id not in parameters
                and isinstance(value, ast.Tuple) and value.elts
                and all(isinstance(item, ast.Constant)
                        and type(item.value) in (int, str, bytes, bool, type(None))
                        for item in value.elts)):
            continue
        occurrences = [part for part in parts if isinstance(part, ast.Name) and part.id == target.id]
        if all(part is target or isinstance(part.ctx, ast.Load)
               and isinstance(parents.get(part), ast.Compare)
               and all(isinstance(op, (ast.Eq, ast.NotEq)) for op in parents[part].ops)
               for part in occurrences):
            hidden.add(value)
    return hidden



def _private_function_reference(node, parents):
    """Only immediate unpacking or a literal element index hides the return wrapper."""
    parent = parents.get(node)
    consumer = parents.get(parent)
    unpacked = (isinstance(consumer, ast.Assign) and consumer.value is parent
                and len(consumer.targets) == 1 and flat_unpacking(consumer.targets[0]))
    indexed = (isinstance(consumer, ast.Subscript) and consumer.value is parent
               and isinstance(consumer.ctx, ast.Load)
               and (isinstance(consumer.slice, ast.Constant) and type(consumer.slice.value) is int
                    or isinstance(consumer.slice, ast.UnaryOp) and isinstance(consumer.slice.op, ast.USub)
                    and isinstance(consumer.slice.operand, ast.Constant)
                    and type(consumer.slice.operand.value) is int))
    return isinstance(parent, ast.Call) and parent.func is node and (unpacked or indexed)


def globally_private_return_tuple_displays(module):
    """Keep shared helper ASTs fresh only if every relevant caller hides the wrapper.

    Any stored, aliased, forwarded or identity-observing use requires the pool.
    Script-only __main__ tests do not execute during modeled function calls.
    """
    functions = {node.name: node for node in module.body if isinstance(node, ast.FunctionDef)}
    roots = []
    for statement in module.body:
        test = statement.test if isinstance(statement, ast.If) else None
        main_guard = (isinstance(test, ast.Compare) and len(test.ops) == 1
                      and isinstance(test.ops[0], ast.Eq) and len(test.comparators) == 1
                      and isinstance(test.left, ast.Name) and test.left.id == '__name__'
                      and isinstance(test.comparators[0], ast.Constant)
                      and test.comparators[0].value == '__main__')
        roots.extend(statement.orelse if main_guard else [statement])
    parts = [part for root in roots for part in ast.walk(root)]
    parents = {child: parent for parent in parts for child in ast.iter_child_nodes(parent)}
    uses = {}
    for node in parts:
        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load) and node.id in functions:
            uses.setdefault(node.id, []).append(_private_function_reference(node, parents))
    return {node.value for name, private in uses.items() if private and all(private)
            for node in ast.walk(functions[name])
            if isinstance(node, ast.Return) and isinstance(node.value, ast.Tuple)}


def unpacked_return_tuple_displays(module, entry):
    """
    Hide returned tuple wrappers only when every reachable use immediately
    unpacks them or reads one element with a literal integer index. The entry
    function's own return remains observable. Forwarding, aliases, slices,
    dynamic indices, and discarded calls do not qualify.
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
            consumed = _private_function_reference(node, parents)
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
