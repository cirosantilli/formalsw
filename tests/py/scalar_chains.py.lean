import «.formalsw».tests.py.«scalar_chains.py.ast»
import lang.py.FormalSW.ScalarComparisons

namespace tests.py.scalar_chains
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := ScalarChainsAst.module

/-- A false first comparison skips the division, including at the zero denominator. -/
theorem guarded.result (n : Int) :
    ReturnsValue program "guarded" [.int n] (.bool (decide (0 < n ∧ n < 1 / n))) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  by_cases positive : 0 < n
  · simp only [positive, true_and]
    apply Evaluates.chain Evaluates.constant
    apply Evaluates.Compares.next (Evaluates.lookup rfl) (by simp [scalarCompare, evalCmpOp, positive])
    apply Evaluates.Compares.last (value := .int (1 / n))
    · exact Evaluates.binary Evaluates.constant (Evaluates.lookup rfl)
        (by simp [scalarBinary, positive, show n ≠ 0 by omega])
    · simp [scalarCompare, evalCmpOp]
  · simp only [positive, false_and, decide_false]
    apply Evaluates.chain Evaluates.constant
    exact Evaluates.Compares.stop (Evaluates.lookup rfl) (by simp [scalarCompare, evalCmpOp, positive])

theorem guarded.«Returns» (n : Int) : (Calls.function program "guarded" [.int n]).Returns :=
  (guarded.result n).returns

end tests.py.scalar_chains
