def count(xs: list[int]) -> int:
    """
    @formalsw: Returns
    """
    total = 0
    for x in reversed(xs):
        total += 1
    return total
