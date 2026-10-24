def identity(n: int) -> int:
    return n


def maximum(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    return max(range(n + 1), key=identity)
