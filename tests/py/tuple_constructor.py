def copy(values: list[int]) -> tuple[int, ...]:
    """
    @formalsw: Returns
    """
    return tuple(values)


def empty() -> tuple[int, ...]:
    """
    @formalsw: Returns
    """
    return tuple()


if __name__ == "__main__":
    assert copy([]) == ()
    assert copy([2, 3, 2]) == (2, 3, 2)
    assert empty() == ()
