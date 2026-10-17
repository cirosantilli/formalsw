def offset(n: int, step: int = 10) -> int:
    """
    @formalsw: Returns
    """
    return n + step


def reference(n: int) -> int:
    return n + 10


def shifted(n: int) -> int:
    """
    @formalsw: Equiv(reference)
    """
    return offset(n)


def combined(n: int) -> int:
    """
    @formalsw: Returns
    """
    return offset(n, 2) + offset(n)


if __name__ == '__main__':
    assert shifted(-13) == -3
    assert combined(4) == 20
