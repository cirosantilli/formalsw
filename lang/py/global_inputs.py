"""Module bindings used as explicit call-entry inputs by the stateful models."""
import ast
from dataclasses import dataclass
import symtable
from lang.py.call_graph import call_targets


class GlobalInputError(ValueError):
    def __init__(self, node, message):
        super().__init__(message)
        self.line = getattr(node, 'lineno', 1)


@dataclass(frozen=True)
class GlobalInput:
    name: str
    kind: str


@dataclass(frozen=True)
class RecordInput:
    origin: str
    name: str
    frozen: bool
    fields: tuple[tuple[str, str], ...]


def annotation_record(annotation):
    """A nominal domain resolved from a validated source class, never a bare name."""
    return getattr(annotation, 'formalsw_record_input', None)


def annotation_domain(annotation):
    """Signature equality retains class identity and its declared field domains."""
    return annotation_record(annotation) or annotation_kind(annotation) or ast.dump(annotation or ast.Constant(None))


def structured_kind(kind):
    """Select the recursive heap domain without changing existing flat domains."""
    scalar_kinds = ('int', 'str', 'bytes', 'bool', 'None')
    flat_dictionaries = {f'dict[{key},{value}]' for key in scalar_kinds for value in scalar_kinds}
    return bool(kind and ('tuple[' in kind or 'dict[' in kind and kind not in flat_dictionaries))


def _structured_annotation_kind(annotation):
    if isinstance(annotation, ast.Constant) and annotation.value is None:
        return 'None'
    if isinstance(annotation, ast.Name) and annotation.id in ('int', 'str', 'bytes', 'bool'):
        return annotation.id
    if not isinstance(annotation, ast.Subscript) or getattr(annotation.value, 'formalsw_typing_invalid', False):
        return None
    container = getattr(annotation.value, 'formalsw_typing_container', None)
    if container is None and isinstance(annotation.value, ast.Name):
        container = annotation.value.id
    if container == 'list':
        element = _structured_annotation_kind(annotation.slice)
        return f'list[{element}]' if element is not None else None
    if container == 'dict':
        fields = annotation.slice.elts if isinstance(annotation.slice, ast.Tuple) else []
        if len(fields) != 2:
            return None
        key, value = (_structured_annotation_kind(field) for field in fields)
        if key is None or value is None or any(token in key for token in ('list[', 'dict[')):
            return None
        return f'dict[{key},{value}]'
    if container != 'tuple':
        return None
    fields = annotation.slice.elts if isinstance(annotation.slice, ast.Tuple) else [annotation.slice]
    if not fields:
        return 'tuple[()]'
    if len(fields) == 2 and isinstance(fields[1], ast.Constant) and fields[1].value is Ellipsis:
        element = _structured_annotation_kind(fields[0])
        return f'tuple[{element},...]' if element is not None else None
    kinds = [_structured_annotation_kind(field) for field in fields]
    return 'tuple[' + ','.join(kinds) + ']' if all(kind is not None for kind in kinds) else None


def container_type_term(kind):
    """Render a validated canonical annotation as a Lean structural domain."""
    try:
        annotation = ast.parse(kind, mode='eval').body
    except (SyntaxError, TypeError) as error:
        raise ValueError('invalid structural container domain') from error
    if not structured_kind(kind) or _structured_annotation_kind(annotation) != kind:
        raise ValueError('invalid structural container domain')

    def render(node):
        if isinstance(node, ast.Name):
            return f'.scalar "{node.id}"'
        if isinstance(node, ast.Constant):
            return '.scalar "None"'
        if node.value.id == 'list':
            return f'.list ({render(node.slice)})'
        if node.value.id == 'dict':
            key, value = node.slice.elts
            return f'.dictionary ({render(key)}) ({render(value)})'
        fields = node.slice.elts if isinstance(node.slice, ast.Tuple) else [node.slice]
        if len(fields) == 2 and isinstance(fields[1], ast.Constant) and fields[1].value is Ellipsis:
            return f'.tupleOf ({render(fields[0])})'
        return '.tuple [' + ', '.join(render(field) for field in fields) + ']'

    return render(annotation)


def annotation_kind(annotation):
    if annotation_record(annotation) is not None:
        return 'record'
    if isinstance(annotation, ast.Name) and annotation.id in ('int', 'str', 'bytes', 'bytearray', 'bool'):
        return annotation.id
    structured = _structured_annotation_kind(annotation)
    if structured_kind(structured):
        return structured
    if isinstance(annotation, ast.Subscript):
        if getattr(annotation.value, 'formalsw_typing_invalid', False):
            return None
        container = getattr(annotation.value, 'formalsw_typing_container', None)
        if container is None and isinstance(annotation.value, ast.Name):
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


def integer_expression_kind(node, resolve):
    """
    Infer the type of a pure integer initializer without evaluating its value.
    Globals remain call-entry inputs; this does not certify module initialization.
    """
    if isinstance(node, ast.Constant):
        return {int: 'int', bool: 'bool'}.get(type(node.value))
    if isinstance(node, ast.Name):
        kind = resolve(node.id)
        return kind if kind in ('int', 'bool') else None
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub, ast.Invert)):
        return 'int' if integer_expression_kind(node.operand, resolve) else None
    if isinstance(node, ast.BinOp) and isinstance(node.op, (
            ast.Add, ast.Sub, ast.Mult, ast.FloorDiv, ast.Mod,
            ast.BitAnd, ast.BitOr, ast.BitXor, ast.LShift, ast.RShift, ast.Pow)):
        left = integer_expression_kind(node.left, resolve)
        right = integer_expression_kind(node.right, resolve)
        if not left or not right:
            return None
        if isinstance(node.op, ast.Pow) and not (
                isinstance(node.right, ast.Constant) and type(node.right.value) in (int, bool)
                and node.right.value >= 0):
            return None
        if isinstance(node.op, (ast.BitAnd, ast.BitOr, ast.BitXor)) and left == right == 'bool':
            return 'bool'
        return 'int'
    return None


def function_globals(module, function, *, heap_calls=False):
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
    def references(scope):
        names = {symbol.get_name() for symbol in scope.get_symbols()
                 if symbol.is_global() and (symbol.is_referenced() or symbol.is_assigned())}
        for child in scope.get_children():
            names.update(references(child))
        return names
    referenced = references(table)
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
            if structured_kind(expected):
                raise GlobalInputError(stmt, 'tuple-containing globals are not yet supported; pass the container as an argument')
            if expected and expected.startswith('list[list['):
                raise GlobalInputError(stmt, 'nested list globals are not yet supported; pass the list as an argument')
            if expected and expected.startswith('set['):
                raise GlobalInputError(stmt, 'set globals are not yet supported; pass the set as an argument')
            if expected and expected.startswith('dict[') and not heap_calls:
                raise GlobalInputError(stmt, 'dictionary globals are not yet supported; pass the dictionary as an argument')
            if isinstance(value, ast.Name):
                kind = domain(value.id, (*visiting, name))
            elif value is None and expected:
                kind = expected
            elif isinstance(value, (ast.UnaryOp, ast.BinOp)) and (computed := integer_expression_kind(
                    value, lambda alias: domain(alias, (*visiting, name)))) is not None:
                kind = computed
            else:
                try:
                    literal = ast.literal_eval(value)
                except (ValueError, TypeError, SyntaxError):
                    raise GlobalInputError(stmt, f'global {name!r} needs a literal initializer or declared alias') from None
                scalar = {int: 'int', bool: 'bool', str: 'str'}
                if heap_calls:
                    scalar[bytes] = 'bytes'
                kind = scalar.get(type(literal))
                if type(literal) is list:
                    elements = {{int: 'int', bool: 'bool', str: 'str'}.get(type(item)) for item in literal}
                    if not elements and expected and expected.startswith('list['):
                        kind = expected
                    elif len(elements) == 1 and None not in elements:
                        kind = f'list[{elements.pop()}]'
                if heap_calls and type(literal) is dict:
                    dictionary_scalar = {**scalar, type(None): 'None'}
                    keys = {dictionary_scalar.get(type(key)) for key in literal}
                    values = {dictionary_scalar.get(type(item)) for item in literal.values()}
                    if not literal and expected and expected.startswith('dict['):
                        kind = expected
                    elif len(keys) == len(values) == 1 and None not in keys | values:
                        kind = f'dict[{keys.pop()},{values.pop()}]'
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


def call_globals(module, function):
    """
    Collect state used by the entire local call graph, including class methods.
    Function bodies remain responsible for their own lexical local bindings.
    """
    functions = {node.name: node for node in module.body if isinstance(node, ast.FunctionDef)}
    classes = {node.name: node for node in module.body if isinstance(node, ast.ClassDef)}
    pending, visited, groups = [function], set(), []
    while pending:
        current = pending.pop()
        if id(current) in visited:
            continue
        visited.add(id(current))
        if isinstance(current, ast.ClassDef):
            pending.extend(node for node in current.body if isinstance(node, ast.FunctionDef))
            continue
        groups.append(function_globals(module, current, heap_calls=True))
        for arg in current.args.args:
            if isinstance(arg.annotation, ast.Name) and arg.annotation.id in classes:
                pending.append(classes[arg.annotation.id])
        for statement in current.body:
            for node in ast.walk(statement):
                for target in call_targets(node):
                    callee = functions.get(target) or classes.get(target)
                    if callee is not None:
                        pending.append(callee)
    return merge_globals(*groups)


def needs_heap_globals(module, function):
    """Keep legacy global models for simple bodies; calls and dictionaries need a context."""
    if getattr(function, 'formalsw_globals', ()):
        return True
    try:
        inputs = call_globals(module, function)
    except GlobalInputError:
        return False
    if not inputs:
        return False
    if any(item.kind.startswith('dict[') or item.kind == 'bytes' for item in inputs):
        return True
    targets = {node.name for node in module.body if isinstance(node, (ast.FunctionDef, ast.ClassDef))}
    return (bool(function.args.defaults)
            or any(isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in targets
                   for statement in function.body for node in ast.walk(statement)))


def global_input_names(function, inputs):
    """Keep module bindings distinct from identically named function arguments."""
    taken = {'this_function', '_this_module'}
    if function:
        taken.update(arg.arg for arg in function.args.args)
    names = {}
    for item in inputs:
        name = item.name
        if name in taken:
            name = 'global_' + name
        while name in taken:
            name += '_'
        names[item.name] = name
        taken.add(name)
    return names
