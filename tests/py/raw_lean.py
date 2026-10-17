#!/usr/bin/env python
"""@formalsw: theorem module_fact : True"""

def f(n: int) -> int:
    """Identity function.

    @formalsw: theorem returns_input (n : Int) :
      n = n ∧ RawLeanAst.module.findFunctionBody "f" ≠ none

    @formalsw: theorem tests.py.raw_lean.explicit_fact : True

    @formalsw: Returns

    @formalsw: theorem does_not_throw : Not Throws(this_function(n))
    """
    return n


def g(n: int) -> int:
    """A second function can reuse the same short theorem name.

    @formalsw: theorem returns_input : n = n
    @formalsw: Returns
    """
    return n
