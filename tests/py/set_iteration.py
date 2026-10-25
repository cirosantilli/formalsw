#!/usr/bin/env python3


def count(values: set[int]) -> int:
    """
    @formalsw: Returns
    """
    total = 0
    for value in values:
        total += 1
    return total


def fast_count(values: set[int]) -> int:
    """
    @formalsw: Equiv(count)
    """
    return len(values)
