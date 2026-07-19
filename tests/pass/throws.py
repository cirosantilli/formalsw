#!/usr/bin/env python

def reject_odd(n: int) -> int:
    """Return even inputs and throw for odd inputs.

    @cleanxy: Throws
    """
    if n % 2 != 0:
        raise ValueError("odd input")
    return n
