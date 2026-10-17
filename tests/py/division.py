def quotient(n: int, d: int) -> int:
    """
    @formalsw: Requires(d != 0)
    @formalsw: Returns
    """
    return n // d


def remainder(n: int, d: int) -> int:
    """
    @formalsw: Requires(d != 0)
    @formalsw: Returns
    """
    return n % d


def negative(n: int) -> int:
    """
    @formalsw: Returns
    """
    return n % -2


def augmented(n: int, d: int) -> int:
    """
    @formalsw: Requires(d != 0)
    @formalsw: Returns
    """
    n //= d
    return n


if __name__ == '__main__':
    assert quotient(7, -3) == -3
    assert quotient(-7, -3) == 2
    assert remainder(7, -3) == -2
    assert remainder(-7, -3) == -1
    assert negative(7) == -1
    assert augmented(7, -3) == -3
