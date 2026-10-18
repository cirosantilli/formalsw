import «.formalsw».tests.py.«stepped_ranges.py.ast»
import FormalSW

namespace tests.py.stepped_ranges
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := SteppedRangesAst.module

private theorem increment_result (n : Int) :
    ReturnsValue program "increment" [.int n] (.int (n + 1)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary])

private def body : List Stmt :=
  [.assign [.name "n"] (.constant (.int 0)),
   .assign [.name "k"] (.constant (.int 42)),
   .assign [.name "total"] (.call (.name "increment") [.name "total"])]
private def otherwise : List Stmt := [.return (.name "total")]

private theorem loop_result (k : Nat) (total : Int) (env : ScalarEnv)
    (ht : env "total" = some (.int total)) :
    BlockReturns program env [.rangeStepLoop "k" k 0 (-1) body otherwise] (.int (total + k)) := by
  induction k generalizing total env with
  | zero =>
      apply BlockReturns.range_done (by simp [rangeContinues])
      simpa using BlockReturns.return_value (rest := []) (module := program) (Evaluates.lookup ht)
  | succ k ih =>
      apply BlockReturns.range_step (by simp [rangeContinues])
      apply BlockReturns.assign Evaluates.constant
      apply BlockReturns.assign Evaluates.constant
      apply BlockReturns.assign (value := .int (total + 1))
      · exact Evaluates.call (.cons (Evaluates.lookup (by simpa [ScalarEnv.set] using ht)) .nil)
          (increment_result total)
      · simpa [Int.natCast_add, Int.add_assoc, Int.add_comm, Int.add_left_comm] using
          ih (total + 1) _ (by simp [ScalarEnv.set])

private theorem countdown_result (n : Nat) :
    ReturnsValue program "countdown" [.int n] (.int n) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign Evaluates.constant
  apply BlockReturns.for_range (values := [.int n, .int 0, .int (-1)])
  · exact .cons (Evaluates.lookup rfl) (.cons Evaluates.constant (.cons
      (Evaluates.unary Evaluates.constant rfl) .nil))
  · rfl
  · simpa using loop_result n 0 _ rfl

theorem countdown.«Returns» (n : Int) (hn : n ≥ 0) :
    (Calls.function program "countdown" [.int n]).Returns := by
  simpa [Int.toNat_of_nonneg hn] using (countdown_result n.toNat).returns

private theorem first_result (n : Int) :
    ReturnsValue program "first" [.int n] (.int n) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.for_range (values := [.int n, .int (n + 1)])
  · exact .cons (Evaluates.lookup rfl) (.cons
      (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary])) .nil)
  · rfl
  · apply BlockReturns.range_step (by simp [rangeContinues]; omega)
    exact BlockReturns.return_value (Evaluates.lookup rfl)

theorem first.«Returns» (n : Int) : (Calls.function program "first" [.int n]).Returns :=
  (first_result n).returns

theorem zero_step.throws (n : Int) : (Calls.function program "zero_step" [.int n]).Throws := by
  refine ⟨{ typeName := "ValueError", args := [] }, ?_⟩
  exact Execution.finishes_of_observe (fuel := 20) rfl

theorem ordered.throws (n : Int) : (Calls.function program "ordered" [.int n]).Throws := by
  refine ⟨{ typeName := "ZeroDivisionError", args := [] }, ?_⟩
  exact Execution.finishes_of_observe (fuel := 20) rfl

theorem boolean_bound.«Returns» (n : Int) : (Calls.function program "boolean_bound" [.int n]).Returns := by
  refine ⟨.int n, ?_⟩
  exact Execution.finishes_of_observe (fuel := 20) rfl

theorem single_bound.«Returns» (n : Int) (hn : n ≥ 0) :
    (Calls.function program "single_bound" [.int n]).Returns := by
  apply ReturnsValue.returns (value := .int 0)
  apply BlockReturns.function rfl rfl
  apply BlockReturns.for_range (values := [.int (n + 1)])
  · exact .cons (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (increment_result n)) .nil
  · rfl
  · apply BlockReturns.range_step (by simp [rangeContinues]; omega)
    exact BlockReturns.return_value (Evaluates.lookup rfl)

theorem typed_order.throws (n : Int) : (Calls.function program "typed_order" [.int n]).Throws := by
  refine ⟨{ typeName := "ZeroDivisionError", args := [] }, ?_⟩
  exact Execution.finishes_of_observe (fuel := 20) rfl

end tests.py.stepped_ranges
