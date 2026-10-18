def reference(xs: list[int]) -> list[int]:
    return xs


def identity(xs: list[int]) -> list[int]:
    """
    @formalsw: Requires(len(xs) >= 0)
    @formalsw: Returns
    @formalsw: Equiv(reference)
    @formalsw: ReturnType
    @formalsw: theorem raw : Returns(this_function(xs))
    """
    return xs


def keep(left: list[int], right: list[int]) -> list[int]:
    """
    @formalsw: Returns
    """
    return right
