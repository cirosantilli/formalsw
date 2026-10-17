def present(n: int, xs: list[int]) -> bool:
    """
    @formalsw: Returns
    """
    return n in xs


def absent(n: int, xs: list[int]) -> bool:
    """
    @formalsw: Returns
    """
    return n not in xs


def restored(n: int, xs: list[int]) -> bool:
    """
    @formalsw: Equiv(present)
    """
    return not (n not in xs)


def literal(n: int) -> bool:
    """
    @formalsw: Returns
    """
    return n in (4, 6, 9, 11)
