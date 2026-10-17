#!/usr/bin/env python3
"""Plain-Python constant-space model of range.

@formalsw theorem modeled : RangeAst.module.hasExactlyClassMethods "range" ["__init__", "__len__", "__contains__", "__getitem__"] = true
@formalsw theorem source_fingerprint : RangeAst.module.fingerprint = 6424005208048408203
"""


class range:
    def __init__(self, start: int, stop: int, step: int):
        assert step != 0
        self.start = start
        self.stop = stop
        self.step = step

    def __len__(self) -> int:
        if self.step > 0:
            if self.start >= self.stop:
                return 0
            return (self.stop - self.start - 1) // self.step + 1
        if self.start <= self.stop:
            return 0
        return (self.start - self.stop - 1) // -self.step + 1

    def __contains__(self, value: int) -> bool:
        if self.step > 0:
            return self.start <= value and value < self.stop and (value - self.start) % self.step == 0
        return self.stop < value and value <= self.start and (value - self.start) % self.step == 0

    def __getitem__(self, index: int) -> int:
        if index < 0:
            index = index + len(self)
        if index < 0 or index >= len(self):
            raise IndexError()
        return self.start + self.step * index
