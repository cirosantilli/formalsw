#!/usr/bin/env python
"""@cleanxy: theorem module_fact : True"""

def f(n: int) -> int:
    """Identity function.

    @cleanxy: theorem returns_input (n : Int) :
      n = n ∧ RawLeanAst.module.findFunctionBody "f" ≠ none

    @cleanxy: theorem tests.py.raw_lean.explicit_fact : True

    @cleanxy: Returns

    @cleanxy: theorem does_not_throw : Not Throws(this_function(n))
    """
    return n


def g(n: int) -> int:
    """A second function can reuse the same short theorem name.

    @cleanxy: theorem returns_input : n = n
    @cleanxy: Returns
    """
    return n
