def add(left: int, right: int = 7) -> int:
    return left + right


def expanded(a: int, b: int) -> int:
    """
    @formalsw: Returns
    """
    return add(*(a, b))


def omitted(a: int) -> int:
    """
    @formalsw: Returns
    """
    return add(*[a])
