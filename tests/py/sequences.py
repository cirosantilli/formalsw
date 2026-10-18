def product(xs: list[int]) -> int:
    p = 1
    for x in xs:
        p *= x
    return p


def square(n: int) -> int:
    """
    @formalsw: Equiv(reference)
    """
    return product([n, n])


def reference(n: int) -> int:
    return n * n


def text_length(s: str) -> int:
    """
    @formalsw: Returns
    """
    return len(s)
