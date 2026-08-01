#!/usr/bin/env python3
"""Plain-Python set facades over the primitive balanced-tree store.

@cleanxy theorem modeled : SetAst.module.hasExactlyClassMethods "set" ["__init__", "__len__", "__contains__", "add", "discard", "clear", "copy"] = true ∧ SetAst.module.hasExactlyClassMethods "frozenset" ["__init__", "__len__", "__contains__", "copy"] = true
@cleanxy theorem source_fingerprint : SetAst.module.fingerprint = 2446208541726633312
"""


class set:
    def __init__(self, tree):
        self.tree = tree

    def __len__(self) -> int:
        return self.tree.size()

    def __contains__(self, value) -> bool:
        return self.tree.contains(value)

    def add(self, value):
        self.tree = self.tree.insert(value)

    def discard(self, value):
        self.tree = self.tree.erase(value)

    def clear(self):
        self.tree = self.tree.clear()

    def copy(self):
        return set(self.tree)


class frozenset:
    def __init__(self, tree):
        self.tree = tree

    def __len__(self) -> int:
        return self.tree.size()

    def __contains__(self, value) -> bool:
        return self.tree.contains(value)

    def copy(self):
        return self
