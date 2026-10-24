def identity(value):
    return value


def push(items, value):
    items.append(value)
    return value


def nonnegative(value):
    return value >= 0


def scalar_entry(n: int) -> int:
    """
    @formalsw: Returns
    """
    return identity(n)


def heap_entry(items: list[int], value: int) -> int:
    """
    @formalsw: Returns
    """
    return push(items, value)


def guarded_entry(n: int) -> int:
    """
    @formalsw: Requires(nonnegative(n))
    @formalsw: Returns
    """
    return identity(n)
