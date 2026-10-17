#!/usr/bin/env python3
"""Plain-Python mutable byte sequence over the primitive list model.

@formalsw theorem modeled : BytearrayAst.module.hasExactlyClassMethods "bytearray" ["__init__", "__len__", "__getitem__", "append", "clear", "extend", "reverse"] = true
@formalsw theorem source_fingerprint : BytearrayAst.module.fingerprint = 4966000535727619840
"""


class bytearray:
    def __init__(self, value: list[int]):
        self.value = value

    def __len__(self) -> int:
        return len(self.value)

    def __getitem__(self, index: int) -> int:
        return self.value[index]

    def append(self, byte: int):
        self.value = self.value + [byte]

    def clear(self):
        self.value = []

    def extend(self, other: "bytearray"):
        self.value = self.value + other.value

    def reverse(self):
        self.value = list(reversed(self.value))
