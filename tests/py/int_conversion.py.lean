import «.formalsw».tests.py.«int_conversion.py.ast»
import FormalSW

namespace tests.py.int_conversion
open FormalSW.PyAst
private abbrev program := IntConversionAst.module

theorem identity.«Returns» (n : Int) : (Calls.function program "identity" [.int n]).Returns :=
  ⟨.int n, Execution.finishes_of_observe (fuel := 20) rfl⟩

theorem identity.«Supported» (n : Int) : (Calls.function program "identity" [.int n]).Supported :=
  (identity.«Returns» n).supported

theorem heap_identity.«Returns» (n : Int) : (HeapCalls.scalarFunction program "heap_identity" [.int n]).Returns :=
  ⟨.int n, Execution.finishes_of_observe (fuel := 40) rfl⟩

theorem heap_identity.«Supported» (n : Int) : (HeapCalls.scalarFunction program "heap_identity" [.int n]).Supported :=
  (heap_identity.«Returns» n).supported

theorem root.result (n : Nat) :
    Calls.ReturnsValue program "root" [.int n] (.int (Math.isqrt n)) := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  apply Calls.Evaluates.builtin (values := [.int (Math.isqrt n)])
  · apply Calls.Evaluates.Arguments.cons
    · apply Calls.Evaluates.qualified_call
      apply Calls.Evaluates.library_call (.cons (Calls.Evaluates.lookup rfl) .nil) rfl
      change some (Math.isqrtCall [.int n]) = _
      simp [Math.isqrtCall]
    · exact .nil
  · rfl

theorem root.«Returns» (n : Int) (requires : Calls.Condition program
    (fun name => if name = "n" then some (.int n) else none) IntConversionAst.requires_root_0) :
    (Calls.function program "root" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare requires rfl
  simpa [Int.toNat_of_nonneg nonnegative] using (root.result n.toNat).returns

theorem root.«Supported» (n : Int) (requires : Calls.Condition program
    (fun name => if name = "n" then some (.int n) else none) IntConversionAst.requires_root_0) :
    (Calls.function program "root" [.int n]).Supported :=
  (root.«Returns» n requires).supported

end tests.py.int_conversion
