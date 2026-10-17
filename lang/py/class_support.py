"""
Validate static plain classes used by the shared-heap interpreter.
"""
import ast
from pathlib import Path

from lang.py.imports import bindings
from lang.py.global_inputs import annotation_kind


def dataclass_fields(module, cls, reject):
    """Resolve the standard decorator and its required positional data fields."""
    if not cls.decorator_list:
        return None

    def fail(message, node=cls):
        reject(node, message)
        return None

    if len(cls.decorator_list) != 1:
        return fail('dataclasses require a single standard-library decorator')
    decorator = cls.decorator_list[0]
    target, frozen = decorator, False
    if isinstance(decorator, ast.Call):
        target = decorator.func
        if (decorator.args or len(decorator.keywords) > 1
                or any(option.arg != 'frozen' or not isinstance(option.value, ast.Constant)
                       or type(option.value.value) is not bool for option in decorator.keywords)):
            return fail('dataclass options support only a literal frozen=True or frozen=False')
        frozen = bool(decorator.keywords and decorator.keywords[0].value.value)
    if isinstance(target, ast.Name):
        definitions = bindings(module, target.id)
        valid = (len(definitions) == 1 and isinstance(definitions[0], ast.ImportFrom)
                 and definitions[0].level == 0 and definitions[0].module == 'dataclasses'
                 and any(alias.name == 'dataclass' and (alias.asname or alias.name) == target.id
                         for alias in definitions[0].names))
    elif isinstance(target, ast.Attribute) and isinstance(target.value, ast.Name) and target.attr == 'dataclass':
        definitions = bindings(module, target.value.id)
        valid = (len(definitions) == 1 and isinstance(definitions[0], ast.Import)
                 and any(alias.name == 'dataclasses' and (alias.asname or alias.name) == target.value.id
                         for alias in definitions[0].names))
    else:
        valid = False
    if not valid:
        return fail('dataclass must resolve to its unmodified standard-library import')
    source = getattr(cls, 'formalsw_origin', getattr(module, 'formalsw_source', None))
    roots = (Path.cwd(),) if source is None else (Path(source).parent, Path.cwd())
    if any((root / 'dataclasses.py').exists() or (root / 'dataclasses').is_dir() for root in roots):
        return fail('a local dataclasses module shadows the modeled standard library')
    fields, names = [], set()
    for node in cls.body:
        if isinstance(node, ast.AnnAssign):
            if not isinstance(node.target, ast.Name) or node.value is not None or not node.simple:
                return fail('dataclass fields require annotations without defaults', node)
            name = node.target.id
            if name.startswith('__') or name in names:
                return fail('dataclass fields require unique ordinary names', node)
            if name == 'bit_length':
                return fail('bit_length is currently reserved for the modeled integer method', node)
            if annotation_kind(node.annotation) is None or any(
                    bindings(module, part.id) for part in ast.walk(node.annotation) if isinstance(part, ast.Name)):
                return fail('dataclass fields need unshadowed supported scalar or container annotations', node)
            names.add(name)
            fields.append(node)
        elif isinstance(node, ast.FunctionDef):
            if node.name.startswith('__') or node.name in names:
                return fail('dataclasses do not support custom special methods or field/method collisions', node)
            names.add(node.name)
        elif not (isinstance(node, ast.Pass) or isinstance(node, ast.Expr)
                  and isinstance(node.value, ast.Constant) and type(node.value.value) is str):
            return fail('dataclass bodies support required fields, ordinary methods, and docstrings', node)
    # Class-local methods can shadow the annotation names during class creation.
    methods = {node.name for node in cls.body if isinstance(node, ast.FunctionDef)}
    if any(part.id in methods for field in fields for part in ast.walk(field.annotation) if isinstance(part, ast.Name)):
        return fail('class methods must not shadow dataclass field annotations')
    return frozen, fields


def plain_class_methods(module, cls, reject):
    """Keep descriptor hooks, inheritance, and mutable class namespaces explicit."""
    data = dataclass_fields(module, cls, reject)
    if cls.bases or cls.keywords or (cls.decorator_list and data is None) or getattr(cls, 'type_params', []):
        reject(cls, 'heap classes require a plain or supported dataclass definition without bases or type parameters')
    if bindings(module, cls.name) != [cls]:
        reject(cls, 'class constructor bindings must not be rebound')
    for node in ast.walk(module):
        if (isinstance(node, ast.Attribute) and isinstance(node.ctx, (ast.Store, ast.Del))
                and isinstance(node.value, ast.Name) and node.value.id == cls.name):
            reject(node, 'class namespaces must not be mutated')
    methods = []
    names = set()
    for node in cls.body:
        if data is not None and isinstance(node, ast.AnnAssign):
            continue
        if isinstance(node, ast.Pass) or (isinstance(node, ast.Expr)
                and isinstance(node.value, ast.Constant) and type(node.value.value) is str):
            continue
        if not isinstance(node, ast.FunctionDef):
            reject(node, 'plain class bodies support methods and docstrings; class attributes are unsupported')
            continue
        if node.name in names:
            reject(node, 'class methods require unique names')
        names.add(node.name)
        if node.name.startswith('__') and node.name != '__init__':
            reject(node, 'custom special methods and private-name mangling are unsupported')
        if node.name == 'bit_length':
            reject(node, 'bit_length is currently reserved for the modeled integer method')
        if not node.args.args:
            reject(node, 'instance methods require a receiver parameter')
        methods.append(node)
    return methods


def ordinary_attribute(node, reject):
    """Avoid Python descriptors and class-private name rewriting."""
    if node.attr.startswith('__'):
        reject(node, 'special attributes and private-name mangling are unsupported')
