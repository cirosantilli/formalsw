#!/usr/bin/env python3


def reference(n: int) -> int:
    """
    @formalsw: Returns
    """
    return 1


def difference(n: int) -> int:
    """
    @formalsw: Returns
    @formalsw: Equiv(reference)
    """
    pair = (n, n + 1)
    first, second = pair
    return second - first
