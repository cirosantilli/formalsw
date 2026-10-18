from math import isqrt as integer_root


def root(n: int) -> int:
    """@formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    return integer_root(n)


def negative(n: int) -> int:
    """@formalsw: theorem throws (n : Int) (_hn : n < 0) : Throws(this_function(n))"""
    return integer_root(n)


def boolean_root(flag: bool) -> int:
    """@formalsw: Returns"""
    return integer_root(flag)


def bad_type(n: str) -> int:
    """@formalsw: theorem throws (n : String) : Throws(this_function(n))"""
    return integer_root(n)


if __name__ == '__main__':
    for n in range(1000):
        r = root(n)
        assert r * r <= n < (r + 1) * (r + 1)
    assert root(10 ** 100) == 10 ** 50
    assert boolean_root(True) == 1
    assert boolean_root(False) == 0
    for function, value, exception in ((negative, -5, ValueError), (bad_type, '1', TypeError)):
        try:
            function(value)
        except exception:
            pass
        else:
            raise AssertionError(function.__name__)
