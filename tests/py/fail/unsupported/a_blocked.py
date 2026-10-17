"""Unsupported obligations must be counted even without a Lean proof file."""


def unsupported_call(n: int) -> int:
    """
    @cleanxy: Not Halts
    @cleanxy: Not Throws
    @cleanxy: theorem irrelevant : True
    """
    return abs(n)


def unreachable(n: int) -> int:
    """@cleanxy: Returns"""
    if False:
        print(n)
    return n


def equivalent(n: int) -> int:
    """@cleanxy: Not Equiv(unsupported_call)"""
    return n
