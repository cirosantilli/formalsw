def increment(n: int) -> int:
    return n + 1


def countdown(n: int) -> int:
    """@formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    total = 0
    for k in range(n, 0, -1):
        n = 0
        k = 42
        total = increment(total)
    else:
        return total


def first(n: int) -> int:
    """@formalsw: Returns"""
    for k in range(n, n + 1):
        return k
    return -1


def zero_step(n: int) -> int:
    """@formalsw: theorem throws (n : Int) : Throws(this_function(n))"""
    for k in range(n, n, 0):
        return k
    return -1


def forever(n: int) -> int:
    while True:
        n += 1


def ordered(n: int) -> int:
    """@formalsw: theorem throws (n : Int) : Throws(this_function(n))"""
    for k in range(1 // 0, forever(n), 0):
        return k
    return -1


def boolean_bound(n: int) -> int:
    """@formalsw: Returns"""
    for k in range(False, True):
        return n
    return -1


def single_bound(n: int) -> int:
    """@formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    for k in range(increment(n)):
        return k
    return -1


def typed_order(n: int) -> int:
    """@formalsw: theorem throws (n : Int) : Throws(this_function(n))"""
    for k in range("not an index", 1 // 0):
        return k
    return n


if __name__ == '__main__':
    for n in range(25):
        assert countdown(n) == n
        assert first(n - 15) == n - 15
        assert boolean_bound(n) == n
        assert single_bound(n) == 0
        for function, exception in ((zero_step, ValueError), (ordered, ZeroDivisionError),
                                    (typed_order, ZeroDivisionError)):
            try:
                function(n)
            except exception:
                pass
            else:
                raise AssertionError(function.__name__)
