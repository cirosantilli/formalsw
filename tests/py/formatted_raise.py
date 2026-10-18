def describe(n: int) -> str:
    """
    @formalsw: Returns
    @formalsw: ReturnType
    """
    return f"value {n}"


def reject(n: int) -> int:
    """
    @formalsw: Halts
    @formalsw: Throws
    """
    raise ValueError(f"value {n}")
