def copied(values: list[int], reverse: bool) -> list[int]:
    """
    @formalsw: Returns
    """
    return sorted(values, reverse=reverse)


def in_place(values: list[int], reverse: bool) -> list[int]:
    """
    @formalsw: Returns
    """
    values.sort(reverse=reverse)
    return values


def generated(values: list[int]) -> list[int]:
    """
    @formalsw: Returns
    """
    return sorted((value for value in values), reverse=True)


if __name__ == "__main__":
    assert copied([2, 1, 3], True) == [3, 2, 1]
    assert in_place([2, 1, 3], False) == [1, 2, 3]
    assert generated([2, 1, 3]) == [3, 2, 1]
