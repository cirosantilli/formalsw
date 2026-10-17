def flags(n: int) -> bytearray:
    """
    @formalsw: Returns
    """
    return bytearray(b"\x01") * n


def first_zero(n: int) -> bytearray:
    """
    @formalsw: Requires(n >= 1)
    @formalsw: Returns
    """
    values = flags(n)
    values[0] = 0
    return values


def first_flag(n: int) -> int:
    """
    @formalsw: Requires(n >= 1)
    @formalsw: Returns
    """
    return flags(n)[0]
