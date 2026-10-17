"""
Validate static plain classes used by the shared-heap interpreter.
"""
import ast

from lang.py.imports import bindings


def plain_class_methods(module, cls, reject):
    """Keep descriptor hooks, inheritance, and mutable class namespaces explicit."""
    if cls.bases or cls.keywords or cls.decorator_list or getattr(cls, 'type_params', []):
        reject(cls, 'heap classes require an undecorated definition without bases or type parameters')
    if bindings(module, cls.name) != [cls]:
        reject(cls, 'class constructor bindings must not be rebound')
    for node in ast.walk(module):
        if (isinstance(node, ast.Attribute) and isinstance(node.ctx, (ast.Store, ast.Del))
                and isinstance(node.value, ast.Name) and node.value.id == cls.name):
            reject(node, 'class namespaces must not be mutated')
    methods = []
    names = set()
    for node in cls.body:
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
