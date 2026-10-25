def empty(n: int) -> bytes:
    """
    @formalsw: Returns
    """
    return bytes()


def copy(value: bytes) -> bytes:
    """
    @formalsw: Returns
    """
    return bytes(value)


def normalized(n: int) -> bytes:
    """
    @formalsw: Returns
    """
    return bytes((n % 256, 0, 255))
