def copy(table: dict[str, int]) -> dict[str, int]:
    """
    @formalsw: Returns
    @formalsw: ReturnType
    """
    return dict(table)


def solve(n: int) -> int:
    """
    @formalsw: Equiv(reference)
    @formalsw: Returns
    """
    original = {"n": n}
    copied = dict(original)
    copied["n"] = n + 1
    return original["n"]


def reference(n: int) -> int:
    return n
