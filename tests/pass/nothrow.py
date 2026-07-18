#!/usr/bin/env python

def reject_odd(n: int) -> int:
    """Return even inputs and throw for odd inputs.

    @cleanxyz: theorem reject_odd_not_noThrow :
      ¬ CleanXYZ.Property.Function.NoThrow NothrowAst.module "reject_odd"
    """
    if n % 2 != 0:
        raise ValueError("odd input")
    return n
