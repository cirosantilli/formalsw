#!/usr/bin/env python
"""Simple and meaningful example of various basic functionality."""

def sum(n: int) -> int:
    """Optimized version of sum_naive.

    @cleanxy: BigO(1)
    @cleanxy: Equiv(sum_naive)
    @cleanxy: ReturnType
    """
    if n <= 0:
        return 0
    return (n * (n - 1)) // 2

def sum_naive(n: int) -> int:
    """Sum of integers from 0 through n - 1. Return 0 if n <= 0.

    @cleanxy: BigO(n)
    @cleanxy: Returns
    """
    total = 0
    for i in range(n):
        total += i
    return total

if __name__ == "__main__":
    for n in [-10, -1, 0, 1, 2, 10]:
        assert sum(n) == sum_naive(n), n
