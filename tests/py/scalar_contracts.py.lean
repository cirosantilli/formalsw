import «.formalsw».tests.py.«scalar_contracts.py.ast»
import lang.py.FormalSW.Runtime

namespace tests.py.scalar_contracts
open FormalSW.PyAst
private abbrev program := ScalarContractsAst.module

theorem integer.«Returns» (value : Int) : (scalarFunction program "integer" [.int value]).Returns := by
  refine ⟨.int value, ?_⟩
  exact Execution.finishes_of_observe (fuel := 1) rfl

theorem boolean.«Returns» (value : Bool) : (scalarFunction program "boolean" [.bool value]).Returns := by
  refine ⟨.bool value, ?_⟩
  exact Execution.finishes_of_observe (fuel := 1) rfl

theorem text.«Returns» (value : String) : (scalarFunction program "text" [.string value]).Returns := by
  refine ⟨.string value, ?_⟩
  exact Execution.finishes_of_observe (fuel := 1) rfl

theorem constant.«Returns» : (scalarFunction program "constant" []).Returns := by
  refine ⟨.int 1, ?_⟩
  exact Execution.finishes_of_observe (fuel := 1) rfl

end tests.py.scalar_contracts
