def original(n: int, d: int) -> int:
    return n


def recombine(n: int, d: int) -> int:
    """
    @formalsw: Requires(d != 0)
    @formalsw: Returns
    @formalsw: Equiv(original)
    """
    quotient, remainder = divmod(n, d)
    return quotient * d + remainder


if __name__ == '__main__':
    assert recombine(7, -3) == 7
    assert recombine(-7, 3) == -7
