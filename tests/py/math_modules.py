import math
import math as arithmetic
from math import gcd as divisor


def root(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    return math.isqrt(n)


def pair(a: int, b: int) -> int:
    """
    @formalsw: Returns
    """
    return arithmetic.gcd(a, b)


def heap_pair(a: int, b: int) -> int:
    """
    @formalsw: Returns
    """
    values = [a, b]
    return arithmetic.gcd(values[0], values[1])


def heap_import(a: int, b: int) -> int:
    """
    @formalsw: Returns
    """
    values = [a, b]
    return divisor(values[0], values[1])
