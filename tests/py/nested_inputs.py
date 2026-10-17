def count_cells(rows: list[list[int]]) -> int:
    """
    @formalsw: Returns
    @formalsw: ReturnType
    """
    total = 0
    for row in rows:
        total += len(row)
    return total


def identity(rows: list[list[list[str]]]) -> list[list[list[str]]]:
    """
    @formalsw: Returns
    @formalsw: ReturnType
    """
    return rows
