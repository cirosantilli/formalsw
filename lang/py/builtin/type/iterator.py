#!/usr/bin/env python3
"""Plain-Python finite iterator state machine.

@formalsw theorem modeled : IteratorAst.module.hasExactlyClassMethods "iterator" ["__init__", "__iter__", "__next__"] = true ∧ IteratorAst.module.hasExactlyClassMethods "async_iterator" ["__init__", "__aiter__", "__anext__"] = true
@formalsw theorem source_fingerprint : IteratorAst.module.fingerprint = 13916440456041736003
"""


class iterator:
    def __init__(self, remaining: list):
        self.remaining = remaining

    def __iter__(self):
        return self

    def __next__(self):
        if len(self.remaining) == 0:
            raise StopIteration()
        value = self.remaining[0]
        self.remaining = self.remaining[1:]
        return value


class async_iterator:
    def __init__(self, remaining: list):
        self.remaining = remaining

    def __aiter__(self):
        return self

    def __anext__(self):
        if len(self.remaining) == 0:
            raise StopAsyncIteration()
        value = self.remaining[0]
        self.remaining = self.remaining[1:]
        return value
