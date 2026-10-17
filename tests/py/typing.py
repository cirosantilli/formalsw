#!/usr/bin/env python3


def merge_sort_untyped(a, b) -> bool:
    """
    Throws e.g. if a is int and b is str. Python wisely refusees to compare them.

    @cleanxy: Throws
    """
    a < b

def merge_sort_int(a: int, b: int) -> bool:
    """
    Typing can be used to prove things.

    @cleanxy: Returns
    """
    a < b

def merge_sort_str(a: str, b: str) -> bool:
    """
    Analogous to merge_sort_int

    @cleanxy: Returns
    """
    a < b
