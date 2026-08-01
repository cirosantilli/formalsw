#!/usr/bin/env python3
"""Plain-Python models of the standard descriptor wrappers.

@cleanxy theorem modeled : DescriptorAst.module.hasExactlyClassMethods "property" ["__init__", "__get__", "__set__", "__delete__"] = true ∧ DescriptorAst.module.hasExactlyClassMethods "classmethod" ["__init__", "__get__"] = true ∧ DescriptorAst.module.hasExactlyClassMethods "staticmethod" ["__init__", "__get__"] = true
@cleanxy theorem source_fingerprint : DescriptorAst.module.fingerprint = 6012450843489875384
"""


class property:
    def __init__(self, get, set, delete):
        self.get = get
        self.set = set
        self.delete = delete

    def __get__(self, owner):
        return self.get(owner)

    def __set__(self, owner, value):
        return self.set(owner, value)

    def __delete__(self, owner):
        return self.delete(owner)


class classmethod:
    def __init__(self, function):
        self.function = function

    def __get__(self, owner):
        return self.function(owner)


class staticmethod:
    def __init__(self, function):
        self.function = function

    def __get__(self, owner):
        return self.function
