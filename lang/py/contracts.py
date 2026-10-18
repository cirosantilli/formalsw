"""Translate explicit scalar input domains without evaluating user Python."""
import ast


class ContractError(ValueError):
    pass


def input_condition(text: str, function: ast.FunctionDef) -> str:
    """Translate a Python integer predicate to a Lean proposition.

    Only total, side-effect-free integer arithmetic is accepted. In particular,
    division and arbitrary calls cannot turn a failing Python expression into a
    false premise that would make the contract vacuous.
    """
    arguments = {arg.arg: arg.annotation for arg in function.args.args}

    def integer(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return f"({node.value} : Int)"
        if isinstance(node, ast.Name) and node.id in arguments:
            annotation = arguments[node.id]
            if isinstance(annotation, ast.Name) and annotation.id == "int":
                return f"«{node.id}»"
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return f"(-{integer(node.operand)})"
        if isinstance(node, ast.BinOp):
            operations = {ast.Add: "+", ast.Sub: "-", ast.Mult: "*"}
            op = operations.get(type(node.op))
            if isinstance(node.op, ast.Mod) and isinstance(node.right, ast.Constant) \
                    and type(node.right.value) is int and node.right.value > 0:
                op = "%"
            if op:
                return f"({integer(node.left)} {op} {integer(node.right)})"
        raise ContractError("Requires accepts integer arguments, constants, +, -, *, and % by a positive constant")

    def predicate(node):
        if isinstance(node, ast.Constant) and type(node.value) is bool:
            return "True" if node.value else "False"
        if isinstance(node, ast.Compare):
            operations = {ast.Eq: "=", ast.NotEq: "≠", ast.Lt: "<", ast.LtE: "≤", ast.Gt: ">", ast.GtE: "≥"}
            terms = [node.left, *node.comparators]
            if all(type(op) in operations for op in node.ops):
                return " ∧ ".join(
                    f"({integer(left)} {operations[type(op)]} {integer(right)})"
                    for left, op, right in zip(terms, node.ops, terms[1:]))
        if isinstance(node, ast.BoolOp):
            op = " ∧ " if isinstance(node.op, ast.And) else " ∨ "
            return op.join(f"({predicate(value)})" for value in node.values)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            return f"¬ ({predicate(node.operand)})"
        raise ContractError("Requires expects a Python integer comparison, and/or/not, or a Boolean constant")

    try:
        return predicate(ast.parse(text, mode="eval").body)
    except SyntaxError as error:
        raise ContractError(f"invalid Requires predicate: {text}") from error
