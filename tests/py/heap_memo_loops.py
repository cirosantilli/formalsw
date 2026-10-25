from functools import lru_cache


@lru_cache(None)
def seed(n: int) -> int:
    return [n][0]


def increment(n: int) -> int:
    """
    @formalsw: Returns
    """
    i = n
    while i < n + 1:
        i += seed(1)
    return i


def sum_seed(n: int) -> int:
    """
    @formalsw: Returns
    """
    return sum(seed(x) for x in [n, n + 1])
