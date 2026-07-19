import «.cleanxy».tests.«raw_lean.py.ast»
import CleanXY

namespace tests.raw_lean

theorem f_returns_input (n : Int) :
    n = n ∧ RawLeanAst.module.findFunctionBody "f" ≠ none := by
  simp [
    CleanXY.PyAst.Module.findFunctionBody,
    CleanXY.PyAst.findFunctionBodyIn,
    RawLeanAst.module,
  ]

end tests.raw_lean
