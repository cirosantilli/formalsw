def power(base: int, exponent: int) -> int:
    """
    @formalsw: Requires(exponent >= 0)
    @formalsw: Returns
    """
    return base ** exponent


def digit_lower(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    return 0 if n == 0 else 10 ** (n - 1)


def square(n: int) -> int:
    """
    @formalsw: Returns
    """
    n **= 2
    return n


def boolean_exponents(n: int) -> int:
    """
    @formalsw: Returns
    """
    return n ** False + n ** True


def ordered(n: int) -> int:
    """
    @formalsw: Throws
    """
    return 'wrong type' ** (n // 0)


def square_reference(n: int) -> int:
    return n * n


def squared(n: int) -> int:
    """
    @formalsw: Equiv(square_reference)
    """
    return power(n, 2)


def guarded(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Requires(10 ** n > 0)
    @formalsw: Returns
    """
    return n


if __name__ == '__main__':
    for n in (-12, -1, 0, 1, 12):
        for exponent in range(8):
            assert power(n, exponent) == n ** exponent
        assert square(n) == n * n
        assert squared(n) == square_reference(n)
        assert boolean_exponents(n) == n + 1
        try:
            ordered(n)
        except ZeroDivisionError:
            pass
        else:
            raise AssertionError('power operands were not evaluated before type validation')
    for n in range(8):
        assert digit_lower(n) == (0 if n == 0 else 10 ** (n - 1))
        assert guarded(n) == n
