def naive(target: set[int], source: list[int]) -> set[int]:
    """
    @formalsw: Returns
    """
    for value in source:
        target.add(value)
    return target


def merge(target: set[int], source: list[int]) -> set[int]:
    """
    @formalsw: Equiv(naive)
    """
    target.update(source)
    return target
