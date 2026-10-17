#!/usr/bin/env python3


def lt_untyped(a, b) -> bool:
    """
    Throws e.g. if a is int and b is str. Python refuses to compare them.

    @cleanxy: Throws
    """
    a < b

def lt_int(a: int, b: int) -> bool:
    """
    Typing can be used to prove things.

    @cleanxy: Returns
    """
    a < b

def lt_str(a: str, b: str) -> bool:
    """
    Analogous to lt_int

    @cleanxy: Returns
    """
    a < b
