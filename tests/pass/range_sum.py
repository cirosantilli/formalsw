#!/usr/bin/env python
"""Small range-sum example used by the Lean AST proof test."""

def sum(n: int) -> int:
    """Return the closed-form sum of Python's `range(n)` for integer `n`.

    @leanpy: NoThrow
    @leanpy: Equiv(sum_naive)
    """
    if n <= 0:
        return 0
    return (n * (n - 1)) // 2

def sum_naive(n: int) -> int:
    """Return the direct loop sum of Python's `range(n)` for integer `n`.

    @leanpy: NoThrow
    """
    total = 0
    for i in range(n):
        total += i
    return total

if __name__ == "__main__":
    for n in [-10, -1, 0, 1, 2, 10]:
        assert sum(n) == sum_naive(n), n
    print(sum(10))
    print(sum_naive(10))
