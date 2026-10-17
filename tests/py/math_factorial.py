import math as arithmetic
from math import factorial as product


def fact(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    return product(n)


def qualified(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Equiv(fact)
    """
    return arithmetic.factorial(n)
