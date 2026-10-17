#!/usr/bin/env python3
"""Plain-Python model of bytes over the primitive list model.

@formalsw theorem modeled : BytesAst.module.hasExactlyClassMethods "bytes" ["__init__", "__eq__", "__lt__", "__le__", "__gt__", "__ge__", "__len__", "__getitem__"] = true
@formalsw theorem source_fingerprint : BytesAst.module.fingerprint = 13820953856544055677
"""


class bytes:
    def __init__(self, value: list[int]):
        self.value = value

    def __eq__(self, other: "bytes") -> bool:
        return self.value == other.value

    def __lt__(self, other: "bytes") -> bool:
        return self.value < other.value

    def __le__(self, other: "bytes") -> bool:
        return self.value <= other.value

    def __gt__(self, other: "bytes") -> bool:
        return self.value > other.value

    def __ge__(self, other: "bytes") -> bool:
        return self.value >= other.value

    def __len__(self) -> int:
        return len(self.value)

    def __getitem__(self, index: int) -> int:
        return self.value[index]
