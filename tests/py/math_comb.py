import math as arithmetic
from math import comb as binomial


def choose(n: int, k: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Requires(k >= 0)
    @formalsw: Returns
    """
    return binomial(n, k)


def qualified(n: int, k: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Requires(k >= 0)
    @formalsw: Equiv(choose)
    """
    return arithmetic.comb(n, k)
