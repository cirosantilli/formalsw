def bits(n: int) -> int:
    """
    @formalsw: Returns
    """
    return n.bit_length()


def missing(s: str) -> int:
    """
    @formalsw: theorem throws : (this_function s).Throws
    """
    return s.bit_length()


def receiver_error(n: int) -> int:
    """
    @formalsw: theorem throws : (this_function n).Throws
    """
    return (1 // 0).bit_length()
