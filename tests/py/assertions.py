def guarded(n: int) -> int:
    """
    @formalsw: Requires(n >= 1)
    @formalsw: Returns
    """
    assert n >= 1, "positive input required"
    return n


def heap_guarded(n: int) -> int:
    """
    @formalsw: Returns
    """
    values = [n]
    assert values, 1 // 0
    return values[0]


def failed(n: int):
    """
    @formalsw: theorem throws (n : Int) : Throws(this_function(n))
    """
    assert False, n
