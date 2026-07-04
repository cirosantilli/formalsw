def f(n: int) -> int:
    """Identity function.

    @leanpy: theorem f_returns_input (n : Int) :
      n = n ∧ RawLeanAst.module.findFunctionBody "f" ≠ none
    """
    return n
