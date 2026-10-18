import «.formalsw».tests.py.«generator_sums.py.ast»
import FormalSW

namespace tests.py.generator_sums
open FormalSW.PyAst
private abbrev program := GeneratorSumsAst.module

theorem scoped.«Returns» (n : Int) :
    (Calls.function program "scoped" [.int n]).Returns := by
  refine ⟨.int (4 + n), ?_⟩
  exact Execution.finishes_of_observe (fuel := 300) rfl

theorem descending.«Returns» (n : Int) :
    (Calls.function program "descending" [.int n]).Returns := by
  refine ⟨.int (0 + n + n + n), ?_⟩
  exact Execution.finishes_of_observe (fuel := 300) rfl

theorem filtered.«Returns» (n : Int) :
    (Calls.function program "filtered" [.int n]).Returns := by
  refine ⟨.int (1), ?_⟩
  exact Execution.finishes_of_observe (fuel := 300) rfl

theorem booleans.«Returns» (n : Int) :
    (Calls.function program "booleans" [.int n]).Returns := by
  refine ⟨.int (1), ?_⟩
  exact Execution.finishes_of_observe (fuel := 300) rfl

theorem nested.«Returns» (n : Int) :
    (Calls.function program "nested" [.int n]).Returns := by
  refine ⟨.int (3), ?_⟩
  exact Execution.finishes_of_observe (fuel := 300) rfl

theorem empty.«Returns» (n : Int) :
    (Calls.function program "empty" [.int n]).Returns := by
  refine ⟨.int (0), ?_⟩
  exact Execution.finishes_of_observe (fuel := 300) rfl

theorem invalid_step.throws (n : Int) :
    (Calls.function program "invalid_step" [.int n]).Throws := by
  refine ⟨{ typeName := "ValueError", args := [] }, ?_⟩
  exact Execution.finishes_of_observe (fuel := 100) rfl

theorem invalid_element.throws (n : Int) :
    (Calls.function program "invalid_element" [.int n]).Throws := by
  refine ⟨{ typeName := "TypeError", args := [] }, ?_⟩
  exact Execution.finishes_of_observe (fuel := 100) rfl

theorem ordered.throws (n : Int) :
    (Calls.function program "ordered" [.int n]).Throws := by
  refine ⟨{ typeName := "ZeroDivisionError", args := [] }, ?_⟩
  exact Execution.finishes_of_observe (fuel := 100) rfl

private def counter (env : ScalarEnv) : Calls.RangeSum :=
  ⟨"x", .constant (.int 1), [], 0, -1, env⟩

private theorem counter_result (env : ScalarEnv) (n : Nat) (total : Int) :
    Calls.SumReturns program (counter env) n total (total + n) := by
  induction n generalizing total with
  | zero =>
      simpa using (Calls.SumReturns.done (module := program) (sum := counter env)
        (next := 0) (total := total) rfl)
  | succ n ih =>
      apply Calls.SumReturns.keep (value := .bool true) (item := .int 1) (updated := total + 1)
      · simp [counter, Calls.rangeContinues]
      · exact Calls.Evaluates.constant
      · rfl
      · exact Calls.Evaluates.constant
      · rfl
      · simpa [counter, Int.natCast_add, Int.natCast_one, Int.add_assoc,
          Int.add_comm, Int.add_left_comm] using ih (total + 1)

theorem countdown.«Returns» (n : Int) :
    (Calls.function program "countdown" [.int n]).Returns := by
  refine Calls.ReturnsValue.returns (value := .int n.toNat)
    (Calls.BlockReturns.function rfl rfl ?_)
  apply Calls.BlockReturns.return_value
  apply Calls.Evaluates.sum_range (values := [.int n, .int 0, .int (-1)])
  · exact .cons (Calls.Evaluates.lookup rfl) (.cons Calls.Evaluates.constant
      (.cons (Calls.Evaluates.unary Calls.Evaluates.constant rfl) .nil))
  · rfl
  · by_cases nonnegative : 0 ≤ n
    · simpa [counter, Int.toNat_of_nonneg nonnegative] using counter_result _ n.toNat 0
    · have negative : n < 0 := Int.lt_of_not_ge nonnegative
      have empty : n.toNat = 0 := Int.toNat_of_nonpos (Int.le_of_lt negative)
      simp only [empty, Int.natCast_zero]
      exact Calls.SumReturns.done (by simp [Calls.rangeContinues, Int.not_lt_of_ge (Int.le_of_lt negative)])

theorem direct.«Returns» (n : Int) :
    (Calls.function program "direct" [.int n]).Returns := by
  refine ⟨.int (6 + n), ?_⟩
  exact Execution.finishes_of_observe (fuel := 300) rfl

theorem direct_descending.«Returns» (n : Int) :
    (Calls.function program "direct_descending" [.int n]).Returns := by
  refine ⟨.int (3 + n), ?_⟩
  exact Execution.finishes_of_observe (fuel := 300) rfl

theorem direct_nested.«Returns» (n : Int) :
    (Calls.function program "direct_nested" [.int n]).Returns := by
  refine ⟨.int (3 + n), ?_⟩
  exact Execution.finishes_of_observe (fuel := 300) rfl

end tests.py.generator_sums
