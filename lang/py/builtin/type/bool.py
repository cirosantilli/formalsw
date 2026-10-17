#!/usr/bin/env python3
"""Plain-Python value model of bool as an integer restricted to zero or one.

@formalsw theorem modeled : BoolAst.module.hasExactlyClassMethods "bool" ["__init__", "__bool__", "__int__", "__index__", "__eq__", "__hash__"] = true
@formalsw theorem source_fingerprint : BoolAst.module.fingerprint = 2967357878154818410
"""


class bool:
    def __init__(self, value):
        if value:
            self.value = 1
        else:
            self.value = 0

    def __bool__(self):
        return self.value != 0

    def __int__(self) -> int:
        return self.value

    def __index__(self) -> int:
        return self.value

    def __eq__(self, other: "bool") -> bool:
        return self.value == other.value

    def __hash__(self) -> int:
        return self.value
