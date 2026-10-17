#!/usr/bin/env python3
"""Plain-Python models of pure and protocol-delegating builtin functions.

The environment-dependent builtins remain explicit Lean runtime interfaces.

@formalsw theorem modeled : FunctionAst.module.hasExactlyFunctions ["_digits", "_format_integer", "bin", "oct", "hex", "chr", "ord", "bool", "repr", "ascii", "format", "all", "any", "len", "iter", "aiter", "next", "anext", "reversed", "enumerate", "filter", "map", "max", "min", "sorted", "zip", "abs", "pow", "sum", "round", "callable", "delattr", "dir", "getattr", "hasattr", "id", "setattr", "vars", "hash", "isinstance", "issubclass", "type", "classmethod", "staticmethod"] = true
@formalsw theorem source_fingerprint : FunctionAst.module.fingerprint = 11409889112085856110
"""


def _digits(value: int, base: int) -> list[int]:
    if value == 0:
        return [48]
    result = []
    while value > 0:
        digit = value % base
        if digit < 10:
            result = [48 + digit] + result
        else:
            result = [87 + digit] + result
        value = value // base
    return result


def _format_integer(value: int, base: int, marker: int) -> list[int]:
    prefix = [48, marker]
    if value < 0:
        return [45] + prefix + _digits(-value, base)
    return prefix + _digits(value, base)


def bin(value: int) -> list[int]:
    return _format_integer(value, 2, 98)


def oct(value: int) -> list[int]:
    return _format_integer(value, 8, 111)


def hex(value: int) -> list[int]:
    return _format_integer(value, 16, 120)


def chr(value: int):
    if value < 0 or value > 1114111:
        raise ValueError()
    return str([value])


def ord(value) -> int:
    if len(value.value) != 1:
        raise TypeError()
    return value.value[0]


def bool(object) -> bool:
    return object.__bool__()


def repr(object):
    return object.__repr__()


def ascii(object):
    return object.__ascii__()


def format(object, specification):
    return object.__format__(specification)


def all(values) -> bool:
    for value in values:
        if not value:
            return False
    return True


def any(values) -> bool:
    for value in values:
        if value:
            return True
    return False


def len(value) -> int:
    return value.__len__()


def iter(value):
    return value.__iter__()


def aiter(value):
    return value.__aiter__()


def next(value):
    return value.__next__()


def anext(value):
    return value.__anext__()


def reversed(value):
    return value.__reversed__()


def enumerate(values, start: int):
    result = []
    index = start
    for value in values:
        result = result + [tuple([index, value])]
        index += 1
    return iter(result)


def filter(predicate, values):
    result = []
    for value in values:
        if predicate(value):
            result = result + [value]
    return iter(result)


def map(function, values):
    result = []
    for value in values:
        result = result + [function(value)]
    return iter(result)


def max(values):
    iterator = iter(values)
    best = next(iterator)
    for value in iterator:
        if best < value:
            best = value
    return best


def min(values):
    iterator = iter(values)
    best = next(iterator)
    for value in iterator:
        if value < best:
            best = value
    return best


def sorted(values):
    result = []
    for value in values:
        index = 0
        while index < len(result) and not value < result[index]:
            index += 1
        result = result[:index] + [value] + result[index:]
    return result


def zip(left, right):
    result = []
    index = 0
    limit = min([len(left), len(right)])
    while index < limit:
        result = result + [tuple([left[index], right[index]])]
        index += 1
    return iter(result)


def abs(number: int) -> int:
    if number < 0:
        return -number
    return number


def pow(base: int, exponent: int) -> int:
    if exponent < 0:
        raise ValueError()
    result = 1
    while exponent > 0:
        result *= base
        exponent -= 1
    return result


def sum(values: list[int], start: int) -> int:
    result = start
    for value in values:
        result += value
    return result


def round(number: int, digits: int) -> int:
    if digits >= 0:
        return number
    factor = pow(10, -digits)
    quotient = number // factor
    remainder = number - quotient * factor
    doubled = 2 * remainder
    if doubled < factor:
        return quotient * factor
    if doubled > factor:
        return (quotient + 1) * factor
    if quotient % 2 == 0:
        return quotient * factor
    return (quotient + 1) * factor


def callable(object) -> bool:
    return object.callable


def delattr(object, name):
    return object.delattr(name)


def dir(object) -> list:
    return object.dir()


def getattr(object, name):
    return object.getattr(name)


def hasattr(object, name) -> bool:
    return object.hasattr(name)


def id(object) -> int:
    return object.identity


def setattr(object, name, value):
    return object.setattr(name, value)


def vars(object):
    return object.attributes


def hash(object) -> int:
    return object.__hash__()


def isinstance(object, type) -> bool:
    return type.is_instance(object)


def issubclass(candidate, target) -> bool:
    return target.is_subclass(candidate)


def type(object):
    return object.type


def classmethod(function):
    return function.__classmethod__()


def staticmethod(function):
    return function.__staticmethod__()
