from functools import lru_cache


def fail(n: int) -> int:
    raise StopIteration(n)


def wrapped(n: int) -> int:
    """
    @formalsw: Throws
    """
    return sum(fail(n) for x in range(1))


def first_iterable(n: int) -> int:
    """
    @formalsw: Throws
    """
    return sum(x for x in range(fail(n)))


def heap_wrapped(n: int) -> int:
    """
    @formalsw: Throws
    """
    return sum(fail(n) for x in [0])


@lru_cache(None)
def cached_fail(n: int) -> int:
    raise StopIteration(n)


def memo_wrapped(n: int) -> int:
    """
    @formalsw: Throws
    """
    return sum(cached_fail(n) for x in range(1))
