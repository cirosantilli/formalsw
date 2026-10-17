def total(n: int) -> int:
    """
    @formalsw: Returns
    @formalsw: ReturnType
    """
    directions: list[tuple[int, int]] = [(0, 1), (1, 0), (1, 1), (1, -1)]
    result: int = 0
    for a, b in directions:
        result += a * n + b
    return result


def annotated(n: int) -> int:
    """
    @formalsw: Returns
    @formalsw: ReturnType
    """
    result: 1 // 0 = n + 1
    result: missing_name
    return result
