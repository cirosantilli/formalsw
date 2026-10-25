def absolute(n: int) -> int:
    """
    @formalsw: Returns
    """
    return abs(n)


def first_tie(n: int) -> int:
    """
    @formalsw: Returns
    """
    return max([n, -n], key=abs)
