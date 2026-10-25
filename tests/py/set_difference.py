#!/usr/bin/env python3


def difference(left: set[int], right: set[int]) -> set[int]:
    """
    @formalsw: Returns
    """
    return left - right


def subtract(left: set[int], right: set[int]) -> set[int]:
    """
    @formalsw: Returns
    """
    left -= right
    return left
