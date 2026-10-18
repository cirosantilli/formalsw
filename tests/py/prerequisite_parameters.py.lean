import «.formalsw».tests.py.«prerequisite_parameters.py.ast»
import FormalSW

namespace tests.py.prerequisite_parameters
open FormalSW.PyAst
private abbrev program := PrerequisiteParametersAst.module

theorem identity.«Returns» (n unused : Int)
    (_requires : Calls.Condition program (fun name => if name = "n" then some (.int n) else none)
      PrerequisiteParametersAst.requires_identity_0) :
    (scalarFunction program "identity" [.int n, .int unused]).Returns :=
  ⟨.int n, Execution.finishes_of_observe (fuel := 10) rfl⟩

/-- Coverage retains the second parameter even though this prerequisite does not use it. -/
theorem requires_identity_0_supported (n _unused : Int) :
    (Calls.evaluate program (fun name => if name = "n" then some (.int n) else none)
      PrerequisiteParametersAst.requires_identity_0).Supported := by
  apply Execution.supported_of_finishes
  apply Calls.Evaluates.finishes (value := .bool (decide (0 ≤ n)))
  apply Calls.Evaluates.compare
    (Calls.Evaluates.builtin (.cons (Calls.Evaluates.lookup rfl) .nil) rfl) Calls.Evaluates.constant
  simp [scalarCompare, evalCmpOp]

end tests.py.prerequisite_parameters
