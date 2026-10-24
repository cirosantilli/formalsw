def weighted(values: list[int], start: int) -> int:
    """
    @formalsw: Returns
    """
    return sum(index * value for index, value in enumerate(values, start=start))
