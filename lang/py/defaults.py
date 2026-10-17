"""Literal immutable defaults, preserved without executing source definitions."""
import ast


def literal_default(expression):
    if isinstance(expression, ast.Constant) and type(expression.value) in (int, bool, str, type(None)):
        return expression.value
    if (isinstance(expression, ast.UnaryOp) and isinstance(expression.op, (ast.USub, ast.UAdd))
            and isinstance(expression.operand, ast.Constant) and type(expression.operand.value) is int):
        value = expression.operand.value
        return -value if isinstance(expression.op, ast.USub) else value
    raise ValueError('default arguments require immutable scalar literals')
