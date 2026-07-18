#!/usr/bin/env python

def double_or_throw(n: int) -> int:
    """Double even inputs and throw for odd inputs.

    @cleanxyz: Equiv(double_or_throw_alt)
    """
    if n % 2 != 0:
        raise ValueError("odd input", n)
    return n * 2


def double_or_throw_alt(n: int) -> int:
    """Alternative implementation with equivalent exception behavior."""
    if n % 2 != 0:
        raise ValueError("odd input", n)
    return n * 2
