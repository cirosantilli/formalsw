def countdown(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    while True:
        if n == 0:
            break
        n -= 1
        continue
        n //= 0
    else:
        return 99
    return n


def first(n: int) -> int:
    """
    @formalsw: Returns
    """
    for k in range(n, n + 3):
        break
    else:
        return 99
    return k


def skip(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    for k in range(n, 0, -1):
        k = 999
        continue
        return -3
    else:
        return n
    return -1


def nested(n: int) -> int:
    """
    @formalsw: Returns
    """
    total = 0
    for a in range(3):
        for b in range(3):
            total += 1
            break
        else:
            total += 100
        total += 10
    else:
        total += 1000
    return total


def inner_else_break(n: int) -> int:
    """
    @formalsw: Returns
    """
    total = 0
    for a in range(3):
        for b in range(0):
            total += 100
        else:
            break
        total += 10
    else:
        total += 1000
    return total


def inner_else_continue(n: int) -> int:
    """
    @formalsw: Returns
    """
    total = 0
    for a in range(3):
        total += 1
        while False:
            total += 100
        else:
            continue
        total += 10
    else:
        total += 1000
    return total


def helper(n: int) -> int:
    for k in range(1):
        break
    return n + 1


def calling(n: int) -> int:
    """
    @formalsw: Returns
    """
    total = 0
    for k in range(3):
        total += helper(n)
        continue
    return total


def return_in_loop(n: int) -> int:
    """
    @formalsw: Returns
    """
    for k in range(3):
        return n
        break
    else:
        return 99
    return 77


def exception_in_loop(n: int) -> int:
    """
    @formalsw: Throws
    """
    while True:
        n //= 0
        break
    return n


def fallthrough(n: int) -> int:
    """
    @formalsw: Returns
    """
    k = 0
    total = 0
    while k < 3:
        k += 1
        if k == 2:
            continue
        if k == 3:
            break
        total += 1
    else:
        total += 1000
    return total


if __name__ == '__main__':
    for n in (0, 1, 2, 10, 100):
        assert countdown(n) == 0
        assert skip(n) == n
    for n in (-10, -1, 0, 1, 10):
        assert first(n) == n
        assert nested(n) == 1033
        assert inner_else_break(n) == 0
        assert inner_else_continue(n) == 1003
        assert calling(n) == 3 * (n + 1)
        assert return_in_loop(n) == n
        assert fallthrough(n) == 1
        try:
            exception_in_loop(n)
        except ZeroDivisionError:
            pass
        else:
            raise AssertionError('missing division by zero')
