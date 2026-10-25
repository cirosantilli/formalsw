"""Retain tuple identities from the protected CPython compilation unit."""
import ast
import dis
import hashlib
from pathlib import Path
import sys
import types


def identify_constant_pools(module, source, text=None):
    """Read compiler constants without executing source, before AST lowering/linking."""
    if sys.implementation.name != 'cpython':
        return
    source = Path(source).resolve()
    text = source.read_text() if text is None else text
    try:
        original = ast.parse(text, filename=str(source))
        if ast.dump(original) != ast.dump(module):
            return
        compiled = compile(text, str(source), 'exec', dont_inherit=True, optimize=0)
    except (SyntaxError, TypeError, ValueError):
        return
    unit = str(source) + ':' + hashlib.sha256(text.encode()).hexdigest() + ':' + sys.implementation.cache_tag
    ordinals, objects = {}, []

    def visit_constant(value):
        if type(value) is tuple:
            if id(value) in ordinals:
                return
            ordinals[id(value)] = len(objects)
            objects.append(value)
            for child in value:
                visit_constant(child)
        elif isinstance(value, types.CodeType):
            for child in value.co_consts:
                visit_constant(child)

    visit_constant(compiled)

    def descriptor(value):
        if type(value) in (int, bool, str, bytes) or value is None:
            return value
        if type(value) is tuple:
            items = [descriptor(child) for child in value]
            return {'identity': unit + ':' + str(ordinals[id(value)]), 'items': items}
        raise ValueError('unsupported compiler constant')

    loaded = {}

    def instructions(code):
        for instruction in dis.get_instructions(code):
            if instruction.opname == 'LOAD_CONST' and type(instruction.argval) is tuple:
                position = instruction.positions
                key = (position.lineno, position.col_offset, position.end_lineno, position.end_col_offset)
                loaded[key] = instruction.argval
        for child in code.co_consts:
            if isinstance(child, types.CodeType):
                instructions(child)

    instructions(compiled)
    def attach(node, value):
        node.formalsw_constant_pool = descriptor(value)
        if len(node.elts) == len(value):
            for child, constant in zip(node.elts, value):
                if isinstance(child, ast.Tuple) and type(constant) is tuple:
                    attach(child, constant)

    for node in ast.walk(module):
        if not isinstance(node, ast.Tuple) or not isinstance(node.ctx, ast.Load):
            continue
        key = (node.lineno, node.col_offset, node.end_lineno, node.end_col_offset)
        value = loaded.get(key)
        if value is not None:
            try:
                attach(node, value)
            except ValueError:
                pass
