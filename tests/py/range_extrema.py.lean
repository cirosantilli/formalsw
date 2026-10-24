import «.formalsw».tests.py.«range_extrema.py.ast»
import FormalSW

namespace tests.py.range_extrema
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := RangeExtremaAst.module

private theorem identity_result (n : Int) :
    ReturnsValue program "identity" [.int n] (.int n) := by
  apply BlockReturns.function rfl rfl
  exact BlockReturns.return_value (Evaluates.lookup rfl)

private theorem scan_returns (count : Nat) (start winner : Int) :
    ∃ result, ExtremumReturns program ⟨true, "identity", start + count, 1⟩ start
      (some (winner, .int winner)) result := by
  induction count generalizing start winner with
  | zero =>
      exact ⟨winner, ExtremumReturns.done (by simp [rangeContinues])⟩
  | succ count ih =>
      let chosen := if start > winner then start else winner
      obtain ⟨result, rest⟩ := ih (start + 1) chosen
      refine ⟨result, ExtremumReturns.next (score := .int start)
        (updated := (chosen, .int chosen)) ?_ (identity_result start) ?_ ?_⟩
      · simp [rangeContinues]
        omega
      · simp [RangeExtremum.choose, scalarCompare, evalCmpOp, chosen]
        split <;> rfl
      · simpa [Int.natCast_add, Int.add_assoc, Int.add_comm, Int.add_left_comm] using rest

private theorem maximum_result (n : Nat) : (function program "maximum" [.int n]).Returns := by
  obtain ⟨result, rest⟩ := scan_returns n 1 0
  apply ReturnsValue.returns (value := .int result)
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.extremum_range (values := [.int (n + 1)])
  · exact .cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary])) .nil
  · rfl
  · apply ExtremumReturns.next (score := .int 0) (updated := (0, .int 0))
    · simp [rangeContinues]
    · exact identity_result 0
    · rfl
    · simpa [Int.add_comm] using rest

theorem maximum.«Returns» (n : Int) (hp : Calls.Condition program
    (fun key => if key = "n" then some (.int n) else none) RangeExtremaAst.requires_maximum_0) :
    (function program "maximum" [.int n]).Returns := by
  have nonnegative : n ≥ 0 := by
    simpa [evalCmpOp] using Evaluates.condition_int_compare hp rfl
  simpa [Int.toNat_of_nonneg nonnegative] using maximum_result n.toNat

end tests.py.range_extrema
