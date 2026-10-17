def count(values: list[int], start: int) -> int:
    """
    @formalsw: Returns
    @formalsw: ReturnType
    """
    total = 0
    for index, value in enumerate(values, start):
        total += 1
    return total
