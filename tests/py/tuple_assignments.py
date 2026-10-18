def swap(n: int) -> int:
    """@formalsw: Returns"""
    a, b = n, n + 1
    a, b = b, a
    return a - b


def repeated(n: int) -> int:
    """@formalsw: Returns"""
    a, a = n, n + 1
    return a


def empty(n: int) -> int:
    """@formalsw: Returns"""
    () = ()
    return n


def forever(n: int) -> int:
    while True:
        n += 1


def ordered(n: int) -> int:
    """@formalsw: theorem throws (n : Int) : Throws(this_function(n))"""
    a, b = 1 // 0, forever(n)
    return a + b


if __name__ == "__main__":
    assert swap(17) == 1
    assert repeated(-5) == -4
    assert empty(12) == 12
    try:
        ordered(0)
    except ZeroDivisionError:
        pass
    else:
        raise AssertionError("the first right-hand side must raise")
