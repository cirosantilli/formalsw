def reference(values: list[int], threshold: int) -> int:
    """
    @formalsw: Returns
    """
    for value in values:
        if value >= threshold:
            return value
    return threshold


def solve(values: list[int], threshold: int) -> int:
    """
    @formalsw: Equiv(reference)
    @formalsw: Returns
    """
    return next((value for value in values if value >= threshold), threshold)
