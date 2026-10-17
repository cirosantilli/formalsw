#!/usr/bin/env python

def reject_odd(n: int) -> int:
    """Return even inputs and throw for odd inputs.

    @formalsw: Halts
    @formalsw: Throws

    @formalsw: theorem throws_at_one : Throws(this_function(1))

    @formalsw: theorem returns_at_zero : Returns(this_function(0))
    """
    if n % 2 != 0:
        raise ValueError("odd input")
    return n
