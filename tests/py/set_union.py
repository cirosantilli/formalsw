#!/usr/bin/env python3


def extended(values: set[int], n: int) -> set[int]:
    """
    @formalsw: Returns
    """
    return values | {n}


def updated(values: set[int], n: int) -> set[int]:
    """
    @formalsw: Returns
    """
    values |= {n}
    return values
