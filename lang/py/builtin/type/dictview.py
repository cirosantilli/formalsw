#!/usr/bin/env python3
"""Plain-Python models of dictionary views over insertion-ordered lists.

@formalsw theorem modeled : DictviewAst.module.hasExactlyClassMethods "dict_keys" ["__init__", "__iter__", "__len__"] = true ∧ DictviewAst.module.hasExactlyClassMethods "dict_values" ["__init__", "__iter__", "__len__"] = true ∧ DictviewAst.module.hasExactlyClassMethods "dict_items" ["__init__", "__iter__", "__len__"] = true
@formalsw theorem source_fingerprint : DictviewAst.module.fingerprint = 14077084308288124826
"""


class dict_keys:
    def __init__(self, values: list):
        self.values = values

    def __iter__(self):
        return iter(self.values)

    def __len__(self) -> int:
        return len(self.values)


class dict_values:
    def __init__(self, values: list):
        self.values = values

    def __iter__(self):
        return iter(self.values)

    def __len__(self) -> int:
        return len(self.values)


class dict_items:
    def __init__(self, values: list):
        self.values = values

    def __iter__(self):
        return iter(self.values)

    def __len__(self) -> int:
        return len(self.values)
