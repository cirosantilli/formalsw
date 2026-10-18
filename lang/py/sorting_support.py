"""Exact recognition for the legacy sorting proof models."""
import ast

MERGE_SORT = '''
def FUNCTION(ARG):
    if len(ARG) <= 1:
        return ARG
    middle = len(ARG) // 2
    left = FUNCTION(ARG[:middle])
    right = FUNCTION(ARG[middle:])
    merged = []
    left_index = 0
    right_index = 0
    while left_index < len(left) and right_index < len(right):
        if left[left_index] <= right[right_index]:
            merged += [left[left_index]]
            left_index += 1
        else:
            merged += [right[right_index]]
            right_index += 1
    return merged + left[left_index:] + right[right_index:]
'''
QUICK_SORT = '''
def FUNCTION(ARG):
    if len(ARG) <= 1:
        return ARG
    pivot = ARG[0]
    less = []
    equal = []
    greater = []
    for value in ARG:
        if value < pivot:
            less += [value]
        else:
            if value > pivot:
                greater += [value]
            else:
                equal += [value]
    return FUNCTION(less) + equal + FUNCTION(greater)
'''


def body_of(function: ast.FunctionDef) -> list[ast.stmt]:
    body = function.body
    if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant):
        if isinstance(body[0].value.value, str):
            return body[1:]
    return body


def matches_sort(function: ast.FunctionDef, template: str) -> bool:
    if len(function.args.args) != 1:
        return False
    expected = ast.parse(template.replace('FUNCTION', function.name).replace('ARG', function.args.args[0].arg)).body[0]
    return [ast.dump(s) for s in body_of(function)] == [ast.dump(s) for s in expected.body]


def uses_sort_model(module, function):
    args = function.args.args
    if len(args) != 1:
        return False
    annotation = args[0].annotation
    base = annotation.value if isinstance(annotation, ast.Subscript) else annotation
    if not isinstance(base, ast.Name) or base.id != 'list':
        return False
    if any(matches_sort(function, template) for template in (MERGE_SORT, QUICK_SORT)):
        return True
    args, body = function.args.args, body_of(function)
    if not (len(args) == 1 and len(body) == 1 and isinstance(body[0], ast.Return)):
        return False
    call = body[0].value
    if not (isinstance(call, ast.Call) and isinstance(call.func, ast.Name) and not call.keywords
            and len(call.args) == 1 and isinstance(call.args[0], ast.Name) and call.args[0].id == args[0].arg):
        return False
    return any(isinstance(target, ast.FunctionDef) and target.name == call.func.id
               and any(matches_sort(target, template) for template in (MERGE_SORT, QUICK_SORT))
               for target in module.body)
