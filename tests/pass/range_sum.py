#!/usr/bin/env python
"""Simple and meaningful example of various basic functionality."""

def sum(n: int) -> int:
    """Optimized version of sum_naive.

    @cleanxyz: Equiv(sum_naive)
    @cleanxyz: Not Throws
    """
    if n <= 0:
        return 0
    return (n * (n - 1)) // 2

def sum_naive(n: int) -> int:
    """Sum of integers from 1 to n. Return 0 if n <= 0."""
    total = 0
    for i in range(n):
        total += i
    return total

if __name__ == "__main__":
    for n in [-10, -1, 0, 1, 2, 10]:
        assert sum(n) == sum_naive(n), n
