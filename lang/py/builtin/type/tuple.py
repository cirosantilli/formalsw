#!/usr/bin/env python3
"""Plain-Python model of tuple over the primitive list model.

@formalsw theorem modeled : TupleAst.module.hasExactlyClassMethods "tuple" ["__init__", "__eq__", "__lt__", "__le__", "__gt__", "__ge__", "__len__", "__getitem__"] = true
@formalsw theorem source_fingerprint : TupleAst.module.fingerprint = 2897589769102299673
"""


class tuple:
    def __init__(self, value: list):
        self.value = value

    def __eq__(self, other: "tuple") -> bool:
        return self.value == other.value

    def __lt__(self, other: "tuple") -> bool:
        return self.value < other.value

    def __le__(self, other: "tuple") -> bool:
        return self.value <= other.value

    def __gt__(self, other: "tuple") -> bool:
        return self.value > other.value

    def __ge__(self, other: "tuple") -> bool:
        return self.value >= other.value

    def __len__(self) -> int:
        return len(self.value)

    def __getitem__(self, index: int):
        return self.value[index]
