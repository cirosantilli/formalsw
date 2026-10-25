from __future__ import annotations


def counter(n: int) -> int:
    """
    @formalsw: Returns
    """
    total = n

    def add(amount: int) -> int:
        nonlocal total
        total += amount
        return total

    add(2)
    add(3)
    return total
