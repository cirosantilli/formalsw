#!/usr/bin/env python3
"""Plain-Python data model for slice.

@formalsw theorem modeled : SliceAst.module.hasExactlyClassMethods "slice" ["__init__"] = true
@formalsw theorem source_fingerprint : SliceAst.module.fingerprint = 13788410798301299466
"""


class slice:
    def __init__(self, start, stop, step):
        self.start = start
        self.stop = stop
        self.step = step
