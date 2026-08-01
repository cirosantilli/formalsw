import «.cleanxy».tests.py.«raw_lean.py.ast»
import CleanXY

namespace tests.py.raw_lean

theorem f_returns_input (n : Int) :
    n = n ∧ RawLeanAst.module.findFunctionBody "f" ≠ none := by
  simp [
    CleanXY.PyAst.Module.findFunctionBody,
    CleanXY.PyAst.findFunctionBodyIn,
    RawLeanAst.module,
  ]

end tests.py.raw_lean
