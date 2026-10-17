def flags(n: int) -> bytes:
    """
    @formalsw: Returns
    """
    return b"\x01" * n


def reverse(n: int) -> bytes:
    """
    @formalsw: Returns
    """
    return (b"\x00\xff" * n)[::-1]


def heap_flags(n: int) -> bytes:
    """
    @formalsw: Returns
    """
    values = [b"\x01"]
    return values[0] * n


def first_byte(n: int) -> int:
    """
    @formalsw: Returns
    """
    return b"\xff"[0] + n


def mixed_text(n: int):
    """
    @formalsw: theorem throws (n : Int) : Throws(this_function(n))
    """
    return b"" + "text"
