import «.leanpy».tests.pass.«raw_lean.py.ast»
import LeanPy

namespace Tests.Pass.RawLean

theorem f_returns_input (n : Int) :
    n = n ∧ RawLeanAst.module.findFunctionBody "f" ≠ none := by
  simp [
    LeanPy.PyAst.Module.findFunctionBody,
    LeanPy.PyAst.findFunctionBodyIn,
    RawLeanAst.module,
  ]

end Tests.Pass.RawLean
