def twice(n: int) -> int:
    return n + n


def scoped(n: int) -> int:
    """
    @formalsw: Returns
    """
    x = n
    return sum(twice(x) for x in range(4) if x % 2 == 0) + x


def descending(n: int) -> int:
    """
    @formalsw: Returns
    """
    return sum(n for x in range(3, 0, -1))


def filtered(n: int) -> int:
    """
    @formalsw: Returns
    """
    return sum(1 // x for x in range(2) if x if True)


def booleans(n: int) -> int:
    """
    @formalsw: Returns
    """
    return sum(True for x in range(True))


def nested(n: int) -> int:
    """
    @formalsw: Returns
    """
    return sum(sum(x for x in range(2)) + x for x in range(2))


def empty(n: int) -> int:
    """
    @formalsw: Returns
    """
    return sum(1 // 0 for x in range(1, 0))


def invalid_step(n: int) -> int:
    """
    @formalsw: theorem throws : (this_function n).Throws
    """
    return sum(x for x in range(0, 1, 0))


def invalid_element(n: int) -> int:
    """
    @formalsw: theorem throws : (this_function n).Throws
    """
    return sum("wrong" for x in range(1))


def ordered(n: int) -> int:
    """
    @formalsw: theorem throws : (this_function n).Throws
    """
    return sum(x for x in range("wrong", 1 // 0))


def countdown(n: int) -> int:
    """
    @formalsw: Returns
    """
    return sum(1 for x in range(n, 0, -1))


def direct(n: int) -> int:
    """
    @formalsw: Returns
    """
    return sum(range(4)) + n


def direct_descending(n: int) -> int:
    """
    @formalsw: Returns
    """
    return sum(range(3, -2, -2)) + n


def direct_nested(n: int) -> int:
    """
    @formalsw: Returns
    """
    return sum(range(sum(range(3)))) + n
