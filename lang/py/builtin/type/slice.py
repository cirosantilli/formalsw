#!/usr/bin/env python3
"""Plain-Python data model for slice.

@cleanxy theorem modeled : SliceAst.module.hasExactlyClassMethods "slice" ["__init__"] = true
@cleanxy theorem source_fingerprint : SliceAst.module.fingerprint = 18103686344632525824
"""


class slice:
    def __init__(self, start, stop, step):
        self.start = start
        self.stop = stop
        self.step = step
