#!/usr/bin/env python

def f(n: int) -> int:
    """Identity function.

    @cleanxyz: theorem f_returns_input (n : Int) :
      n = n ∧ RawLeanAst.module.findFunctionBody "f" ≠ none
    """
    return n
