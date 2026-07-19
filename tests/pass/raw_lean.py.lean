import «.cleanxy».tests.pass.«raw_lean.py.ast»
import CleanXY

namespace tests.pass.raw_lean

theorem f_returns_input (n : Int) :
    n = n ∧ RawLeanAst.module.findFunctionBody "f" ≠ none := by
  simp [
    CleanXY.PyAst.Module.findFunctionBody,
    CleanXY.PyAst.findFunctionBodyIn,
    RawLeanAst.module,
  ]

end tests.pass.raw_lean
