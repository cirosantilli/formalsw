def less(left: tuple[int, ...], right: tuple[int, ...]) -> bool:
    """
    @formalsw: Returns
    @formalsw: ReturnType
    """
    return left < right


def greater(left: tuple[int, ...], right: tuple[int, ...]) -> bool:
    """
    @formalsw: Returns
    @formalsw: ReturnType
    """
    return left > right


if __name__ == "__main__":
    assert less((), (1,))
    assert greater((8, 14), (8, 13))
    assert not greater((5, 4), (5, 4))
