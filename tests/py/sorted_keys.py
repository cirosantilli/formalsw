def identity(items: list[int]) -> list[int]:
    """
    @formalsw: Returns
    """
    return sorted(items, key=lambda value: value)


def negated(items: list[int]) -> list[int]:
    """
    @formalsw: Returns
    """
    return sorted(items, key=lambda value: -value)
