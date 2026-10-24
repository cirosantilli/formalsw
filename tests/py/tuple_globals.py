TABLE: tuple[int, ...] = (99, 100)
ALIAS = TABLE


def read() -> tuple[int, ...]:
    """
    @formalsw: Returns
    @formalsw: ReturnType
    """
    return TABLE


def same() -> bool:
    """
    @formalsw: Returns
    """
    return TABLE is ALIAS
