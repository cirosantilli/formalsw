#!/usr/bin/env python3
"""Plain-Python dict facade over the primitive balanced-tree store.

@formalsw theorem modeled : DictAst.module.hasExactlyClassMethods "dict" ["__init__", "__len__", "__contains__", "__getitem__", "__setitem__", "__delitem__", "clear", "copy", "keys"] = true
@formalsw theorem source_fingerprint : DictAst.module.fingerprint = 13275742418967923092
"""


class dict:
    def __init__(self, tree, order: list):
        self.tree = tree
        self.order = order

    def __len__(self) -> int:
        return len(self.order)

    def __contains__(self, key) -> bool:
        return self.tree.contains(key)

    def __getitem__(self, key):
        return self.tree.get(key)

    def __setitem__(self, key, value):
        if not self.tree.contains(key):
            self.order = self.order + [key]
        self.tree = self.tree.set(key, value)

    def __delitem__(self, key):
        self.tree = self.tree.erase(key)
        result = []
        for current in self.order:
            if current != key:
                result = result + [current]
        self.order = result

    def clear(self):
        self.tree = self.tree.clear()
        self.order = []

    def copy(self):
        return dict(self.tree, self.order)

    def keys(self) -> list:
        return self.order
