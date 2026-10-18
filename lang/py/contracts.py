"""Parse Python preconditions and check them using the ordinary execution model."""
import ast
from copy import deepcopy
from dataclasses import dataclass


class ContractError(ValueError):
    pass


@dataclass(frozen=True)
class InputCondition:
    expression: ast.expr
    arguments: tuple[ast.arg, ...]
    unsupported: tuple
    needs_coverage: bool
    heap: bool = False


def input_condition(text: str, function: ast.FunctionDef | None, module: ast.Module) -> InputCondition:
    """
    A precondition is an ordinary Python expression in the function's input scope.
    Its domain is defined by returning exactly True, including when it calls
    looping or recursive helpers. Coverage checks do not execute user Python.
    """
    try:
        expression = ast.parse(text, mode='eval').body
    except SyntaxError as error:
        raise ContractError(f'invalid Requires predicate: {text}') from error
    # These imports are local because call coverage itself uses import resolution.
    from lang.py.call_support import check_calls, has_partial_primitives, uses_heap_calls
    from lang.py.global_inputs import annotation_kind
    from lang.py.support import UnsupportedConstruct
    names = {node.id for node in ast.walk(expression) if isinstance(node, ast.Name)}
    arguments = tuple(arg for arg in function.args.args if arg.arg in names) if function else ()
    used = {node.id for node in ast.walk(module) if isinstance(node, ast.Name)}
    used.update(node.name for node in module.body if isinstance(node, (ast.FunctionDef, ast.ClassDef)))
    used.update(alias.asname or alias.name.split('.')[0] for node in module.body
                if isinstance(node, (ast.Import, ast.ImportFrom)) for alias in node.names)
    name = '_formalsw_requires'
    while name in used:
        name += '_'
    helper = ast.FunctionDef(name=name,
        args=ast.arguments(posonlyargs=[], args=list(deepcopy(arguments)), vararg=None,
                           kwonlyargs=[], kw_defaults=[], kwarg=None, defaults=[]),
        body=[ast.Return(expression)], decorator_list=[], returns=ast.Name(id='bool', ctx=ast.Load()),
        type_params=[])
    ast.fix_missing_locations(helper)
    context = ast.Module(body=[*module.body, helper], type_ignores=[])
    context.formalsw_source = getattr(module, 'formalsw_source', None)
    issues = []
    def reject(node, reason):
        issues.append(UnsupportedConstruct(function.name if function else '<module>',
            getattr(function, 'lineno', 1), f'Requires: {reason}'))
    heap = uses_heap_calls(context, helper) or bool(function and any(
        reference_kind(annotation_kind(arg.annotation)) for arg in function.args.args))
    check_calls(context, helper, reject, heap=heap)
    return InputCondition(expression, arguments, tuple(dict.fromkeys(issues)),
                          heap or has_partial_primitives(context, helper), heap)


def reference_kind(kind):
    return bool(kind and (kind.startswith('list[') or kind == 'bytearray'))


def heap_input_name(function):
    """Use a fresh binder; argument addresses can alias in this shared entry heap."""
    from lang.py.global_inputs import annotation_kind
    if function is None or not any(reference_kind(annotation_kind(arg.annotation)) for arg in function.args.args):
        return None
    name = '_formalsw_heap'
    names = {arg.arg for arg in function.args.args}
    while name in names:
        name += '_'
    return name
