def at_least(n: int, lower: int) -> bool:
    if lower == 0:
        return n >= 0
    return at_least(n - 1, lower - 1)


def identity(n: int) -> int:
    return n


def guarded(n: int) -> int:
    """
    @formalsw: Requires(at_least(n, 0))
    @formalsw: Returns
    @formalsw: Halts
    @formalsw: Not Throws
    @formalsw: ReturnType
    @formalsw: Equiv(identity)
    @formalsw: EquivReturn(identity)
    @formalsw: BigO(1)
    @formalsw: theorem correct : Returns(this_function(n))
    @formalsw: theorem quantified : ∀ n : Int, Returns(this_function(n))
    @formalsw: theorem witnessed : ∃ n : Int, Returns(this_function(n))
    """
    if n < 0:
        return 1 // 0
    return n


def negative(n: int) -> int:
    """
    @formalsw: Requires(n < 0)
    @formalsw: Throws
    """
    return 1 // 0


def truthy(n: int) -> int:
    """
    @formalsw: Requires(1)
    @formalsw: theorem impossible : False
    """
    return n


def exceptional(n: int) -> int:
    """
    @formalsw: Requires(1 // 0 == 0)
    @formalsw: theorem impossible : False
    """
    return n


def chain(n: int) -> int:
    """
    @formalsw: Requires(0 <= at_least(0, 0) < 2 and True)
    @formalsw: Returns
    """
    return n


def short_chain(n: int) -> int:
    """
    @formalsw: Requires(2 < 1 < 1 // 0)
    @formalsw: theorem impossible : False
    """
    return n


def arithmetic(n: int) -> int:
    """
    @formalsw: Requires(-7 // -3 == 2 and 7 % -3 == -2 and True + 1 == 2 and "a" * 2 == "aa")
    @formalsw: Returns
    """
    return n
