"""
Specialize protected module callbacks without changing their Python source.

Only callback parameters used solely as direct callees are removed. Stable
module bindings make their source function objects known at call entry; every
other argument and the complete helper body retain their evaluation order.
"""
import ast
import copy

from lang.py.defaults import literal_default
from lang.py.imports import bindings


def _bound_names(node):
    """Overapproximate lexical bindings, including nested and comprehension scopes."""
    names = {part.id for part in ast.walk(node)
             if isinstance(part, ast.Name) and isinstance(part.ctx, (ast.Store, ast.Del))}
    names.update(part.arg for part in ast.walk(node) if isinstance(part, ast.arg))
    names.update(part.name for part in ast.walk(node)
                 if isinstance(part, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
                 and part is not node)
    for part in ast.walk(node):
        if isinstance(part, (ast.Import, ast.ImportFrom)):
            names.update(alias.asname or alias.name.split('.')[0] for alias in part.names)
        elif isinstance(part, ast.ExceptHandler) and part.name:
            names.add(part.name)
        elif isinstance(part, (ast.MatchAs, ast.MatchStar)) and part.name:
            names.add(part.name)
        elif isinstance(part, ast.MatchMapping) and part.rest:
            names.add(part.rest)
    return names


def _direct_parameter(function, name):
    """Reject writes, nested captures, aliases, escapes, and indirect callback use."""
    calls = {id(part.func) for statement in function.body for part in ast.walk(statement)
             if isinstance(part, ast.Call) and isinstance(part.func, ast.Name)
             and part.func.id == name}
    if not calls:
        return False
    for statement in function.body:
        for part in ast.walk(statement):
            if isinstance(part, ast.Name) and part.id == name:
                if not isinstance(part.ctx, ast.Load) or id(part) not in calls:
                    return False
            if isinstance(part, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)):
                if any(isinstance(child, ast.Name) and child.id == name
                       or isinstance(child, ast.arg) and child.arg == name
                       for child in ast.walk(part)):
                    return False
                if getattr(part, 'name', None) == name:
                    return False
            if isinstance(part, (ast.Global, ast.Nonlocal)) and name in part.names:
                return False
            if isinstance(part, (ast.Import, ast.ImportFrom)) and any(
                    (alias.asname or alias.name.split('.')[0]) in (name, '*') for alias in part.names):
                return False
            if isinstance(part, ast.ExceptHandler) and part.name == name:
                return False
            if isinstance(part, (ast.MatchAs, ast.MatchStar)) and part.name == name:
                return False
            if isinstance(part, ast.MatchMapping) and part.rest == name:
                return False
    return True


def _plain_helper(function):
    args = function.args
    if (function.decorator_list or getattr(function, 'type_params', []) or args.posonlyargs
            or args.kwonlyargs or args.vararg or args.kwarg
            or any(getattr(arg, 'formalsw_capture', False) for arg in args.args)
            or hasattr(function, 'formalsw_local_function_error')):
        return False
    try:
        for default in args.defaults:
            literal_default(default)
    except ValueError:
        return False
    return len({arg.arg for arg in args.args}) == len(args.args)


def lower_named_callbacks(module):
    """
    Lower finite, nonescaping module-function arguments behind binding guards.

    The original helper remains available and receives no new entry contract.
    Fresh private clones are appended before local import linking, so previously
    proved dependency suffixes retain their complete source definitions.
    """
    if getattr(module, 'formalsw_callbacks_lowered', False):
        return
    module.formalsw_callbacks_lowered = True
    functions = {node.name: node for node in module.body if isinstance(node, ast.FunctionDef)}
    stable = {name: function for name, function in functions.items()
              if bindings(module, name) == [function]}
    occupied = {node.id for node in ast.walk(module) if isinstance(node, ast.Name)}
    occupied.update(node.name for node in ast.walk(module)
                    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)))
    occupied.update(_bound_names(module))
    additions, clones = [], {}

    def specialize(function, chosen):
        signature = (function.name, tuple((index, callback.name) for index, callback in chosen))
        if signature in clones:
            return clones[signature]
        removed = {index for index, _ in chosen}
        replacements = {function.args.args[index].arg: callback.name for index, callback in chosen}
        if any(not _direct_parameter(function, name) for name in replacements):
            return None
        # A newly direct module call must never capture another remaining local.
        locals_ = _bound_names(function) - set(replacements)
        if any(callback.name in locals_ for _, callback in chosen):
            return None
        fresh = '__formalsw_callback_' + function.name + ''.join(
            '_' + function.args.args[index].arg + '_' + callback.name for index, callback in chosen)
        while fresh in occupied:
            fresh += '_'
        occupied.add(fresh)
        clones[signature] = fresh
        # Copy source syntax, not specification environments or cached analyses.
        # Those may contain module objects and must be recomputed for the clone.
        clone = ast.FunctionDef(name=fresh, args=copy.deepcopy(function.args),
            body=copy.deepcopy(function.body), decorator_list=[], returns=copy.deepcopy(function.returns),
            type_params=[])
        ast.copy_location(clone, function)
        clone.formalsw_imported = True
        clone.formalsw_markers = []
        clone.formalsw_callback_origin = function.name
        clone.formalsw_callback_bindings = tuple(dict.fromkeys(
            [function.name, *(callback.name for _, callback in chosen),
             *getattr(function, 'formalsw_callback_bindings', ())]))
        original_count = len(function.args.args)
        default_start = original_count - len(function.args.defaults)
        clone.args.args = [argument for index, argument in enumerate(clone.args.args) if index not in removed]
        clone.args.defaults = [default for index, default in enumerate(clone.args.defaults, default_start)
                               if index not in removed]

        class BindCallback(ast.NodeTransformer):
            def visit_Call(self, node):
                self.generic_visit(node)
                if isinstance(node.func, ast.Name) and node.func.id in replacements:
                    node.func.id = replacements[node.func.id]
                return node

        clone.body = [BindCallback().visit(statement) for statement in clone.body]
        additions.append(clone)
        transform(clone)
        return fresh

    def transform(function):
        if hasattr(function, 'formalsw_local_function_error'):
            return
        locals_ = _bound_names(function)

        class Calls(ast.NodeTransformer):
            # Nested scopes require their own binding analysis. Existing coverage
            # checking handles them; this normalization makes no claim for them.
            def visit_FunctionDef(self, node):
                return node

            def visit_AsyncFunctionDef(self, node):
                return node

            def visit_ClassDef(self, node):
                return node

            def visit_Lambda(self, node):
                return node

            def visit_Call(self, node):
                self.generic_visit(node)
                if (not isinstance(node.func, ast.Name) or node.func.id not in stable
                        or node.func.id in locals_ or node.keywords
                        or any(isinstance(argument, ast.Starred) for argument in node.args)):
                    return node
                target = stable[node.func.id]
                if not _plain_helper(target):
                    return node
                count = len(target.args.args)
                if not count - len(target.args.defaults) <= len(node.args) <= count:
                    return node
                chosen = [(index, stable[argument.id]) for index, argument in enumerate(node.args)
                          if isinstance(argument, ast.Name) and argument.id in stable and argument.id not in locals_]
                if not chosen:
                    return node
                name = specialize(target, chosen)
                if name is not None:
                    removed = {index for index, _ in chosen}
                    node.func.id = name
                    node.args = [argument for index, argument in enumerate(node.args) if index not in removed]
                return node

        function.body = [Calls().visit(statement) for statement in function.body]

    for function in list(functions.values()):
        transform(function)
    module.body.extend(additions)
    ast.fix_missing_locations(module)


def callback_bindings_valid(module, function):
    """Recheck protected identities after helper linking or other AST preparation."""
    origin = getattr(function, 'formalsw_callback_origin', None)
    if origin is not None:
        entries = bindings(module, origin)
        if len(entries) != 1 or not isinstance(entries[0], ast.FunctionDef) or not _plain_helper(entries[0]):
            return False
    for name in getattr(function, 'formalsw_callback_bindings', ()):
        entries = bindings(module, name)
        if len(entries) != 1 or not isinstance(entries[0], ast.FunctionDef) or entries[0] not in module.body:
            return False
    return True


def callback_signature(module, function):
    """Retain original signature hints, including removed callback class annotations."""
    origin = getattr(function, 'formalsw_callback_origin', None)
    entries = bindings(module, origin) if origin is not None else []
    if len(entries) == 1 and isinstance(entries[0], ast.FunctionDef):
        return entries[0].args.args
    return function.args.args
