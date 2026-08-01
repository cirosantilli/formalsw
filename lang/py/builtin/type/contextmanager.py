#!/usr/bin/env python3
"""Plain-Python model of the synchronous context-manager protocol.

@cleanxy theorem modeled : ContextmanagerAst.module.hasExactlyClassMethods "contextmanager" ["__init__", "__enter__", "__exit__"] = true
@cleanxy theorem source_fingerprint : ContextmanagerAst.module.fingerprint = 2344344226781193825
"""


class contextmanager:
    def __init__(self, enter, exit):
        self.enter = enter
        self.exit = exit

    def __enter__(self):
        return self.enter()

    def __exit__(self, exception_type, exception, traceback):
        return self.exit(exception_type, exception, traceback)
