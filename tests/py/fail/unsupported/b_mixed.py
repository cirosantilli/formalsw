"""Supported obligations in this file must still be checked."""


def unsupported_call(n: int) -> int:
    """@cleanxy: Not Halts"""
    return abs(n)


def unsupported_statement(n: int) -> int:
    """@cleanxy: theorem irrelevant : True"""
    try:
        return n
    finally:
        pass


def identity(n: int) -> int:
    """@cleanxy: Returns"""
    return n


def unrelated():
    with open('unused') as source:
        return source.read()
