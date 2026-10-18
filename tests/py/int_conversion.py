import math


def identity(n: int) -> int:
    """
    @formalsw: Returns
    """
    return int(n)


def heap_identity(n: int) -> int:
    """
    @formalsw: Returns
    """
    values = [n]
    return int(values[0])


def root(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    return int(math.isqrt(n))
