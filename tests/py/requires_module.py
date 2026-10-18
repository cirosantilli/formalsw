"""
@formalsw: Requires(True)
@formalsw: theorem established : True
"""


def identity(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    @formalsw: theorem valid : n >= 0
    """
    return n


def no_domain() -> int:
    """
    @formalsw: Requires(False)
    @formalsw: Not Throws
    """
    return 1 // 0
