def eager(values: list[int]) -> list[int]:
    """
    @formalsw: Returns
    """
    return list(values)


def copied(values: list[int]) -> list[int]:
    """
    @formalsw: Equiv(eager)
    """
    return list(value for value in values)


def ordered(values: list[int]) -> list[int]:
    """
    @formalsw: Returns
    """
    return sorted(value for value in values)


def joined(values: list[str]) -> str:
    """
    @formalsw: Returns
    """
    return "".join(value for value in values)
