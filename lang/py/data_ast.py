"""Parse and validate the reusable read-only data interpreter's Python subset.

There is no function-name recognition or source fingerprint. Every accepted
statement is executed by DataRuntime. Validation covers unreachable code too.
"""

import ast
import json
from pathlib import Path
import runpy
import sys


def module_json(source):
    tree = ast.parse(source)
    allowed = (
        ast.Module, ast.FunctionDef, ast.arguments, ast.arg, ast.Return,
        ast.Assign, ast.If, ast.While, ast.Expr, ast.Constant, ast.Name,
        ast.List, ast.Subscript, ast.BinOp, ast.UnaryOp, ast.Compare, ast.Call,
        ast.Load, ast.Store, ast.Add, ast.Sub, ast.Not, ast.USub,
        ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt, ast.GtE,
    )
    for node in ast.walk(tree):
        def reject(reason):
            raise ValueError(f"unsupported Python constructs at line {getattr(node, 'lineno', 1)}: {reason}")
        if not isinstance(node, allowed):
            reject(type(node).__name__)
        if isinstance(node, ast.FunctionDef):
            if node.decorator_list or node.returns is not None:
                reject("decorators or annotations")
            if any(isinstance(child, ast.FunctionDef) for stmt in node.body for child in ast.walk(stmt)):
                reject("nested functions")
        if isinstance(node, ast.arguments):
            if node.posonlyargs or node.kwonlyargs or node.defaults or node.kw_defaults or node.vararg or node.kwarg:
                reject("non-plain arguments")
        if isinstance(node, ast.arg) and node.annotation is not None:
            reject("argument annotation")
        if isinstance(node, ast.Constant) and type(node.value) not in (int, bool, str, type(None)):
            reject("non-scalar literal")
        if isinstance(node, ast.Assign) and (len(node.targets) != 1 or not isinstance(node.targets[0], ast.Name)):
            reject("mutation or destructuring")
        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store) and node.id in ("type", "len", "int", "bool", "str", "list"):
            reject("shadowed builtin")
        if isinstance(node, ast.arg) and node.arg in ("type", "len", "int", "bool", "str", "list"):
            reject("shadowed builtin argument")
        if isinstance(node, ast.Call):
            if not isinstance(node.func, ast.Name) or node.func.id not in ("len", "type") or len(node.args) != 1 or node.keywords:
                reject("only len(value) and type(value) calls are supported")
        if isinstance(node, ast.Compare) and len(node.ops) != 1:
            reject("chained comparison")
    for stmt in tree.body:
        if not isinstance(stmt, ast.FunctionDef) and not (
            isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant) and isinstance(stmt.value.value, str)
        ):
            raise ValueError("unsupported Python constructs: module-level executable code")
    names = [stmt.name for stmt in tree.body if isinstance(stmt, ast.FunctionDef)]
    if len(names) != len(set(names)) or set(names) & {"type", "len", "int", "bool", "str", "list"}:
        raise ValueError("unsupported Python constructs: duplicate or shadowed function name")
    for function in (stmt for stmt in tree.body if isinstance(stmt, ast.FunctionDef)):
        local_names = {arg.arg for arg in function.args.args} | {
            node.id for node in ast.walk(function)
            if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store)
        }
        calls = {id(node.func) for node in ast.walk(function) if isinstance(node, ast.Call)}
        for node in ast.walk(function):
            if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load):
                if node.id in ("type", "len") and id(node) not in calls:
                    raise ValueError("unsupported Python constructs: builtin function used as a value")
                if node.id not in local_names | {"type", "len", "int", "bool", "str", "list"}:
                    raise ValueError(f"unsupported Python constructs: free name {node.id}")
    # Reuse the application's AST schema, rather than introducing a second parser.
    frontend = runpy.run_path(str(Path(__file__).resolve().parents[2] / "formalsw"))
    return frontend["AstJsonEmitter"](tree).emit()


if __name__ == "__main__":
    try:
        print(module_json(json.loads(sys.argv[1])))
    except (ValueError, SyntaxError) as error:
        sys.exit(str(error))
