from functools import lru_cache


@lru_cache(None)
def count(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    if n <= 0:
        return 0
    return 1 + count(n - 1)


def twice(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    return count(n) + count(n)


def guarded(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Requires(count(n) == n)
    @formalsw: Returns
    """
    return n


def same(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Equiv(count)
    """
    return n
