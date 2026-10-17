#!/usr/bin/env python3
"""Plain-Python model of the comparable part of Python's `str`.

@formalsw theorem modeled : StrAst.module.isCodepointStringClass "str" = true
@formalsw theorem source_fingerprint : StrAst.module.fingerprint = 2339401588560382508

Unicode text is represented as a list of integer code points. Python's list
comparison is lexicographic, matching string comparison on code points.
"""


class str:
    """A string represented by Unicode code points."""

    def __init__(self, value: list[int]):
        self.value = value

    def __eq__(self, other: "str") -> bool:
        return self.value == other.value

    def __lt__(self, other: "str") -> bool:
        return self.value < other.value

    def __le__(self, other: "str") -> bool:
        return self.value <= other.value

    def __gt__(self, other: "str") -> bool:
        return self.value > other.value

    def __ge__(self, other: "str") -> bool:
        return self.value >= other.value
