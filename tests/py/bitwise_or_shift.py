def merge(a: int, b: int) -> int:
    """
    @formalsw: Returns
    """
    return a | b


def either(a: bool, b: bool) -> bool:
    """
    @formalsw: Returns
    """
    return a | b


def shift(a: int, count: int) -> int:
    """
    @formalsw: Requires(count >= 0)
    @formalsw: Returns
    """
    return a << count
