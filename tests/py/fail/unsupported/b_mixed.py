"""Supported obligations in this file must still be checked."""


def unsupported_call(n: int) -> int:
    """
    @formalsw: Not Halts
    """
    return round(n)


def unsupported_statement(n: int) -> int:
    """@formalsw: theorem irrelevant : True"""
    try:
        return n
    finally:
        pass


def identity(n: int) -> int:
    """@formalsw: Returns"""
    return n


def unrelated():
    with open('unused') as source:
        return source.read()
