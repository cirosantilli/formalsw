def pair_sum(n: int) -> int:
    """
    @formalsw: Returns
    """
    return sum(x + y for x, y in zip([n], [n + 1]))


def first_pair(n: int) -> int:
    """
    @formalsw: Returns
    """
    for x, y in zip([n], [n + 1]):
        return x + y
    return 0
