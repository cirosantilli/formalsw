#!/usr/bin/env python3


def within(values: list[int], ceiling: int) -> bool:
    """
    @formalsw: Returns
    """
    return all(value <= ceiling for value in values)
