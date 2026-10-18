"""Resolve explicit local function imports for cross-file proof contracts.

This reads source files without importing or executing them. Imported calls in a
function body still need interpreter support; this resolver only identifies the
reference function in an Equiv contract.
"""
import ast
import types
from pathlib import Path
from lang.py.contracts import ContractError


def resolve_python_function(value):
    """Use a setup callable to select a checked, unmodified source definition."""
    if not isinstance(value, types.FunctionType):
        raise ContractError('Equiv setup expression must select a Python source function')
    path = Path(value.__code__.co_filename).resolve()
    if not path.is_file() or not path.is_relative_to(Path.cwd().resolve()):
        raise ContractError(f'Equiv setup function needs a source file inside the current project: {path}')
    text = path.read_text()
    program = ast.parse(text, filename=str(path))
    program.formalsw_source_text = text
    definitions = bindings(program, value.__code__.co_name)
    if len(definitions) != 1 or not isinstance(definitions[0], ast.FunctionDef) or definitions[0] not in program.body:
        raise ContractError('Equiv setup target must be an unmodified module-level function')
    function = definitions[0]
    compiled = compile(text, value.__code__.co_filename, 'exec', dont_inherit=True)
    code = next((constant for constant in compiled.co_consts
                 if isinstance(constant, types.CodeType) and constant.co_name == function.name), None)
    if value.__code__ != code or value.__closure__ or value.__defaults__ or value.__kwdefaults__:
        raise ContractError('Equiv setup target differs from its source definition or captures runtime values')
    return path, program, function


def bindings(module, name):
    """Find module-scope bindings, including conditional rebinding and deletion."""
    found = []

    def visit(node):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if node.name == name:
                found.append(node)
            # Global writes in a function can invalidate an imported identity.
            if any(isinstance(n, ast.Global) and name in n.names for n in ast.walk(node)):
                found.append(node)
            return
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            if any((a.asname or a.name.split('.')[0]) in (name, '*') for a in node.names):
                found.append(node)
            return
        if isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)) and node.id == name:
            found.append(node)
        for child in ast.iter_child_nodes(node):
            visit(child)

    visit(module)
    return found


def find_module(source: Path, module_name: str, level: int = 0) -> Path:
    project = Path.cwd().resolve()
    if not module_name or any(part in ('', '.', '..') for part in module_name.split('.')) \
            or '/' in module_name or '\\' in module_name:
        raise ContractError("Equiv imports need a literal Python module name")
    if level > len(source.resolve().parents):
        raise ContractError("relative Equiv import escapes the source package")
    roots = [source.resolve().parent, project] if level == 0 else [source.resolve().parents[level - 1]]
    candidates = set()
    for root in dict.fromkeys(roots):
        parts = module_name.split('.')
        current = root
        for part in parts[:-1]:
            if (current / (part + '.py')).is_file():
                raise ContractError(f"Equiv package {part!r} is shadowed by a Python module")
            current /= part
            initializer = current / '__init__.py'
            if initializer.is_file():
                body = ast.parse(initializer.read_text(), filename=str(initializer)).body
                if any(not (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant)
                            and isinstance(stmt.value.value, str)) for stmt in body):
                    raise ContractError(f"Equiv import package initialization is unsupported: {initializer}")
        path = current / (parts[-1] + '.py')
        if path.is_file():
            path = path.resolve()
            if not path.is_relative_to(project):
                raise ContractError(f"Equiv import is outside the current project: {path}")
            candidates.add(path)
    if len(candidates) == 1:
        return candidates.pop()
    if candidates:
        raise ContractError(f"ambiguous local Equiv import {module_name!r}")
    raise ContractError(f"cannot resolve local Equiv import {module_name!r} from {source}")


def resolve_function(source: Path, module: ast.Module, name: str):
    """Return (source, AST, function) for an unambiguous local Python import."""
    candidates = bindings(module, name)
    if len(candidates) != 1:
        raise ContractError(f"Equiv target {name!r} must have exactly one binding and must not be rebound")
    binding = candidates[0]
    module_name = function_name = None
    level = 0
    if isinstance(binding, ast.ImportFrom) and binding in module.body:
        alias = next((a for a in binding.names if (a.asname or a.name) == name), None)
        if alias is None:
            raise ContractError("Equiv references require explicit imports; wildcard imports are unsupported")
        module_name, function_name, level = binding.module, alias.name, binding.level
    else:
        assignment = next((stmt for stmt in module.body if isinstance(stmt, ast.Assign)
                           and len(stmt.targets) == 1 and stmt.targets[0] is binding), None)
        value = assignment.value if assignment else None
        if isinstance(value, ast.Attribute) and isinstance(value.value, ast.Call):
            call = value.value
            if isinstance(call.func, ast.Name) and len(call.args) == 1 and not call.keywords \
                    and isinstance(call.args[0], ast.Constant) and isinstance(call.args[0].value, str):
                loaders = bindings(module, call.func.id)
                if len(loaders) == 1 and isinstance(loaders[0], ast.ImportFrom) \
                        and loaders[0] in module.body and loaders[0].level == 0 \
                        and loaders[0].module == 'importlib' and any(
                            a.name == 'import_module' and (a.asname or a.name) == call.func.id
                            for a in loaders[0].names):
                    module_name, function_name = call.args[0].value, value.attr
    if module_name is None:
        raise ContractError(f"Equiv target {name!r} needs a direct from-import or import_module('module').function binding")
    path = find_module(source, module_name, level)
    program = ast.parse(path.read_text(), filename=str(path))
    definitions = bindings(program, function_name)
    if len(definitions) != 1 or not isinstance(definitions[0], ast.FunctionDef) or definitions[0] not in program.body:
        raise ContractError(f"Equiv target {function_name!r} must be an unmodified module-level function in {path}")
    return path, program, definitions[0]
