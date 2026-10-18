#!/usr/bin/env python3


def direct(values: list[int], start: int) -> int:
    """
    @formalsw: Returns
    """
    return sum(values, start)


def generated(values: list[int], start: int) -> int:
    """
    @formalsw: Returns
    @formalsw: Equiv(direct)
    """
    return sum((x for x in values), start=start)


def roundtripped(values: list[int], start: int) -> int:
    """
    @formalsw: Returns
    @formalsw: Equiv(direct)
    """
    return sum((int(str(x)) for x in values), start)
