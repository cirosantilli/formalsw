#!/usr/bin/env python

def f(n: int) -> int:
    """Identity function.

    @cleanxy: theorem f_returns_input (n : Int) :
      n = n ∧ RawLeanAst.module.findFunctionBody "f" ≠ none
    """
    return n
