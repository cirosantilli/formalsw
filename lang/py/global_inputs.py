"""Python's symbol table determines which names denote module state."""

import ast
from dataclasses import dataclass
import symtable


class GlobalInputError(ValueError):
    def __init__(self, node, message):
        super().__init__(message)
        self.line = getattr(node, "lineno", 1)


@dataclass(frozen=True)
class GlobalInput:
    name: str
    kind: str


def function_globals(module, function):
    # Parse ordinary Python scoping, including assignments later in the body.
    try:
        table = next(child for child in symtable.symtable(
            ast.unparse(function), "<function>", "exec").get_children()
            if child.get_type() == "function" and child.get_name() == function.name)
    except SyntaxError as error:
        raise GlobalInputError(function, f"invalid Python scope: {error.msg}") from None
    except StopIteration:
        raise GlobalInputError(function, "generic function scopes are unsupported") from None
    referenced = {
        symbol.get_name() for symbol in table.get_symbols()
        if symbol.is_global() and (symbol.is_referenced() or symbol.is_assigned())
    }
    declared = {symbol.get_name() for symbol in table.get_symbols() if symbol.is_declared_global()}
    definitions = {}
    for stmt in module.body:
        if isinstance(stmt, ast.Assign):
            for target in stmt.targets:
                if isinstance(target, ast.Name):
                    definitions.setdefault(target.id, []).append((stmt, None, stmt.value))
        elif isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
            definitions.setdefault(stmt.target.id, []).append((stmt, stmt.annotation, stmt.value))
    inputs = []
    for name in sorted(referenced | declared):
        entries = definitions.get(name)
        if entries is None:
            if name in declared:
                raise GlobalInputError(function, f"global {name!r} needs a module-level scalar declaration")
            continue  # Unknown names/callees remain subject to normal coverage checks.
        kinds = set()
        for stmt, annotation, value in entries:
            if isinstance(stmt, ast.Assign) and (len(stmt.targets) != 1 or not isinstance(stmt.targets[0], ast.Name)):
                raise GlobalInputError(stmt, f"global {name!r} needs a simple scalar declaration")
            try:
                literal = ast.literal_eval(value) if value is not None else None
            except (ValueError, TypeError, SyntaxError):
                raise GlobalInputError(stmt, f"global {name!r} needs a scalar literal initializer") from None
            kind = {int: "int", bool: "bool", str: "str"}.get(type(literal))
            if kind is None:
                raise GlobalInputError(stmt, f"global {name!r}: only int, str, and bool state is currently supported")
            if annotation is not None and not (isinstance(annotation, ast.Name) and annotation.id == kind):
                raise GlobalInputError(stmt, f"global {name!r}: annotation must match its scalar initializer")
            kinds.add(kind)
        if len(kinds) != 1:
            raise GlobalInputError(entries[-1][0], f"global {name!r} has inconsistent scalar declarations")
        inputs.append(GlobalInput(name, kinds.pop()))
    return tuple(inputs)


def merge_globals(*groups):
    return tuple(sorted({item for group in groups for item in group}, key=lambda item: item.name))
