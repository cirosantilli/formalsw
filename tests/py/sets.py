#!/usr/bin/env python3


def singleton(n: int) -> set[int]:
    """
    @formalsw: Returns
    @formalsw: ReturnType
    """
    values = set()
    values.add(n)
    return values


def insert(values: set[int], n: int) -> None:
    """
    @formalsw: Returns
    """
    values.add(n)


def duplicate(values: set[int], n: int) -> None:
    """
    @formalsw: Equiv(insert)
    """
    values.add(n)
    values.add(n)
