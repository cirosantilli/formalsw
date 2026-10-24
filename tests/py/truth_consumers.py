#!/usr/bin/env python3


def positive(values: list[int]) -> bool:
    """
    @formalsw: Returns
    """
    return all(value > 0 for value in values)
