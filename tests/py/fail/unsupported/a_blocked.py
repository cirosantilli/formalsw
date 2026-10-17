"""Unsupported obligations must be counted even without a Lean proof file."""


def unsupported_call(n: int) -> int:
    """
    @formalsw: Not Halts
    @formalsw: Not Throws
    @formalsw: theorem irrelevant : True
    """
    return abs(n)


def unreachable(n: int) -> int:
    """@formalsw: Returns"""
    if False:
        print(n)
    return n


def equivalent(n: int) -> int:
    """@formalsw: Not Equiv(unsupported_call)"""
    return n
