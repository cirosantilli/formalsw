"""
Typed records retain arbitrary contents and may share objects in the input heap.
"""
from dataclasses import dataclass


@dataclass(frozen=True)
class Record:
    value: int
    items: list[int]


def read(record: Record) -> int:
    """
    @formalsw: Returns
    """
    return record.value


def copied(record: Record) -> int:
    """
    @formalsw: Equiv(read)
    """
    value = record.value
    return value


def total(left: Record, right: Record) -> int:
    """
    @formalsw: Returns
    """
    return left.value + right.value


def guarded(record: Record) -> int:
    """
    @formalsw: Requires(record.value >= 0)
    @formalsw: Equiv(read)
    """
    return record.value
