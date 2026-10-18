#!/usr/bin/env python3


def reference(n: int, key: int) -> int:
    return n


def roundtrip(n: int, key: int) -> int:
    """
    @formalsw: Returns
    @formalsw: Equiv(reference)
    """
    table = {True: 0, key: n}
    alias = table
    alias[key] = n + 1
    return table.get(key, 0) - 1
