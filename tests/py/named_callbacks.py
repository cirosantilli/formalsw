def increment(n: int) -> int:
    return n + 1


def apply_twice(callback, value):
    return callback(callback(value))


def twice_increment(n: int) -> int:
    """
    @formalsw: Returns
    @formalsw: ReturnType
    """
    return apply_twice(increment, n)
