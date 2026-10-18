"""Module bindings used as explicit call-entry inputs by the stateful models."""
import ast
from dataclasses import dataclass
import symtable


class GlobalInputError(ValueError):
    def __init__(self, node, message):
        super().__init__(message)
        self.line = getattr(node, 'lineno', 1)


@dataclass(frozen=True)
class GlobalInput:
    name: str
    kind: str


def annotation_kind(annotation):
    if isinstance(annotation, ast.Name) and annotation.id in ('int', 'str', 'bytes', 'bytearray', 'bool'):
        return annotation.id
    if isinstance(annotation, ast.Subscript) and isinstance(annotation.value, ast.Name):
        container = annotation.value.id
        if container == 'dict' and isinstance(annotation.slice, ast.Tuple) and len(annotation.slice.elts) == 2:
            kinds = tuple('None' if isinstance(part, ast.Constant) and part.value is None
                          else annotation_kind(part) for part in annotation.slice.elts)
            if all(kind in ('int', 'str', 'bytes', 'bool', 'None') for kind in kinds):
                return f'dict[{kinds[0]},{kinds[1]}]'
            return None
        element = annotation_kind(annotation.slice)
        if element in ('int', 'str', 'bool') and container in ('list', 'set'):
            return f'{container}[{element}]'
        if container == 'list' and element and element.startswith('list['):
            return f'list[{element}]'
    return None


def function_globals(module, function):
    """Use Python's scope analysis; infer domains without fixing entry values.

    List declarations establish an element domain, not distinct object identities.
    Aliases in declarations are accepted; entry aliases are universally quantified.
    """
    try:
        table = next(child for child in symtable.symtable(ast.unparse(function), '<function>', 'exec').get_children()
                     if child.get_type() == 'function' and child.get_name() == function.name)
    except SyntaxError as error:
        raise GlobalInputError(function, f'invalid Python scope: {error.msg}') from None
    except StopIteration:
        raise GlobalInputError(function, 'generic function scopes are unsupported') from None
    referenced = {symbol.get_name() for symbol in table.get_symbols()
                  if symbol.is_global() and (symbol.is_referenced() or symbol.is_assigned())}
    declared = {symbol.get_name() for symbol in table.get_symbols() if symbol.is_declared_global()}
    definitions = {}
    for stmt in module.body:
        if isinstance(stmt, ast.Assign):
            for target in stmt.targets:
                if isinstance(target, ast.Name):
                    definitions.setdefault(target.id, []).append((stmt, None, stmt.value))
        elif isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
            definitions.setdefault(stmt.target.id, []).append((stmt, stmt.annotation, stmt.value))

    def domain(name, visiting=()):
        if name in visiting:
            raise GlobalInputError(function, f'cyclic global declarations involving {name!r}')
        if name not in definitions:
            raise GlobalInputError(function, f'global {name!r} needs a module-level declaration')
        kinds = set()
        for stmt, annotation, value in definitions[name]:
            if isinstance(stmt, ast.Assign) and (len(stmt.targets) != 1 or not isinstance(stmt.targets[0], ast.Name)):
                raise GlobalInputError(stmt, f'global {name!r} needs a simple declaration')
            expected = annotation_kind(annotation)
            if expected and expected.startswith('list[list['):
                raise GlobalInputError(stmt, 'nested list globals are not yet supported; pass the list as an argument')
            if expected and expected.startswith('set['):
                raise GlobalInputError(stmt, 'set globals are not yet supported; pass the set as an argument')
            if expected and expected.startswith('dict['):
                raise GlobalInputError(stmt, 'dictionary globals are not yet supported; pass the dictionary as an argument')
            if isinstance(value, ast.Name):
                kind = domain(value.id, (*visiting, name))
            elif value is None and expected:
                kind = expected
            else:
                try:
                    literal = ast.literal_eval(value)
                except (ValueError, TypeError, SyntaxError):
                    raise GlobalInputError(stmt, f'global {name!r} needs a literal initializer or declared alias') from None
                scalar = {int: 'int', bool: 'bool', str: 'str'}
                kind = scalar.get(type(literal))
                if type(literal) is list:
                    elements = {scalar.get(type(item)) for item in literal}
                    if not elements and expected and expected.startswith('list['):
                        kind = expected
                    elif len(elements) == 1 and None not in elements:
                        kind = f'list[{elements.pop()}]'
                if kind is None:
                    raise GlobalInputError(stmt, f'global {name!r}: supported state is int, str, bool, or homogeneous scalar lists; empty lists need list[int], list[str], or list[bool] annotations')
            if annotation is not None and expected != kind:
                raise GlobalInputError(stmt, f'global {name!r}: annotation must match its initializer')
            kinds.add(kind)
        if len(kinds) != 1:
            raise GlobalInputError(definitions[name][-1][0], f'global {name!r} has inconsistent declarations')
        return kinds.pop()

    return tuple(GlobalInput(name, domain(name)) for name in sorted(referenced | declared)
                 if name in definitions or name in declared)


def merge_globals(*groups):
    return tuple(sorted({item for group in groups for item in group}, key=lambda item: item.name))
