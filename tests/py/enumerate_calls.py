def count(values: list[int], start: int) -> int:
    """
    @formalsw: Returns
    @formalsw: ReturnType
    """
    total = 0
    for index, value in enumerate(values, start):
        total += 1
    return total


def first_index(values: list[int], start: int) -> int:
    """
    @formalsw: Returns
    @formalsw: ReturnType
    """
    for index, value in enumerate(values, start):
        return index
    return start - 1


def first_zero(values: list[int]) -> int:
    """
    @formalsw: Returns
    @formalsw: ReturnType
    """
    for index, value in enumerate(values):
        return index
    return -1
