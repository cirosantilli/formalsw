"""
Frozen records preserve their declared fields and compare those fields by value.
"""
from dataclasses import dataclass


@dataclass(frozen=True)
class Point:
    x: int
    y: int


def read(n: int) -> int:
    """
    @formalsw: Returns
    """
    point = Point(n, n + 1)
    return point.x


def equal(n: int) -> bool:
    """
    @formalsw: Returns
    """
    return Point(n, n + 1) == Point(n, n + 1)
