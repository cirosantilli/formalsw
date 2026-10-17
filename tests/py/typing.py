#!/usr/bin/env python3


def lt_untyped(a, b) -> bool:
    """
    Throws e.g. if a is int and b is str. Python refuses to compare them.

    @formalsw: Throws
    """
    a < b

def lt_int(a: int, b: int) -> bool:
    """
    Typing can be used to prove things.

    @formalsw: Returns
    """
    a < b

def lt_str(a: str, b: str) -> bool:
    """
    Analogous to lt_int

    @formalsw: Returns
    """
    a < b
