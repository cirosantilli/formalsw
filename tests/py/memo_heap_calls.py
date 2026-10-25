from functools import lru_cache


@lru_cache(None)
def double(n: int) -> int:
    """
    @formalsw: Returns
    """
    return n + n


def caller(n: int) -> int:
    """
    @formalsw: Requires(len([double(n)]) == 1)
    @formalsw: Returns
    """
    values = [double(n)]
    return double(n) + len(values)
