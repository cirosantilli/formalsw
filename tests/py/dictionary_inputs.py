def reference(table: dict[int, str]) -> dict[int, str]:
    return table


def identity(table: dict[int, str]) -> dict[int, str]:
    """
    @formalsw: Requires(len(table) >= 0)
    @formalsw: Returns
    @formalsw: Equiv(reference)
    @formalsw: ReturnType
    """
    return table


def lookup(table: dict[int, str], key: int) -> str:
    """
    @formalsw: Returns
    @formalsw: ReturnType
    """
    return table.get(key, "")


def replace(table: dict[int, str], key: int, value: str) -> dict[int, str]:
    """
    @formalsw: Returns
    @formalsw: ReturnType
    """
    table[key] = value
    return table
