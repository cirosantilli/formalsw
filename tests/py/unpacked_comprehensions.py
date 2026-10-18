def pair_sum(n: int) -> int:
    """
    @formalsw: Returns
    """
    return sum(x + y for x, y in [[n, n + 1]])
