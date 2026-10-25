from __future__ import annotations


def count(n: int) -> int:
    """
    @formalsw: Returns
    """
    total = 0

    def tick() -> int:
        nonlocal total
        total += 1
        return total

    def down(k: int) -> int:
        if k <= 0:
            return total
        tick()
        return down(k - 1)

    down(n)
    return total
