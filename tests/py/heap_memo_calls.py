from functools import lru_cache


@lru_cache(None)
def cached_pair(n: int) -> tuple[int, int]:
    return n, n + 1


def first_component(n: int) -> int:
    """
    @formalsw: Returns
    """
    return cached_pair(n)[0]
