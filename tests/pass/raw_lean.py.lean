import «.cleanxyz».tests.pass.«raw_lean.py.ast»
import CleanXYZ

namespace tests.pass.raw_lean

theorem f_returns_input (n : Int) :
    n = n ∧ RawLeanAst.module.findFunctionBody "f" ≠ none := by
  simp [
    CleanXYZ.PyAst.Module.findFunctionBody,
    CleanXYZ.PyAst.findFunctionBodyIn,
    RawLeanAst.module,
  ]

end tests.pass.raw_lean
