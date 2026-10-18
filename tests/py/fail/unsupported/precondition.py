def unavailable(n: int) -> bool:
    print(n)
    return True


def guarded(n: int) -> int:
    """
    @formalsw: Requires(False and unavailable(n))
    @formalsw: Returns
    @formalsw: theorem unrelated : True
    """
    return n
