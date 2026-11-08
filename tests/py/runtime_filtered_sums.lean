import lang.py.FormalSW.CallsRuntimeCostFilteredSums

namespace FilteredSumRuntimeRegression
open FormalSW.PyAst Calls Calls.Runtime

private def program : Module := { body := [] }
private def range (n : Nat) : RangeSum :=
  ⟨"i", .name "i", [.compare (.binOp (.name "i") .mod (.constant (.int 2)))
    [(.eq, .constant (.int 0))]], n, 1, fun _ => none⟩

private theorem tested (n : Nat) (i : Int) :
    EvaluatesIn .word program ((range n).env.set "i" (.int i)) (range n).filter 14
      (.bool (decide (i % 2 = 0))) := by
  apply EvaluatesIn.boolean_single (cost := 12) .and
  apply EvaluatesIn.compare (ca := 6) (cb := 1) (av := .int (i % 2)) (bv := .int 0)
  · exact EvaluatesIn.binary (work := 1) (av := .int i) (bv := .int 2)
      (EvaluatesIn.lookup (by simp [ScalarEnv.set])) EvaluatesIn.constant
      (by simp [scalarBinary]) rfl
  · exact EvaluatesIn.constant
  · simp [scalarCompare, evalCmpOp]

/-- Rejected candidates still incur work; the selected indices sum to at most n². -/
theorem bounded (n : Nat) :
    ∃ cost answer, 7 * n + 4 ≤ cost ∧ cost ≤ 27 * n + 4 ∧
      0 ≤ answer ∧ answer ≤ (n : Int) * n ∧
      ∀ stack, RuntimeCost.Reaches (step program) (charge .word program)
        ⟨.sumLoop (range n) 0 0, stack⟩ cost ⟨.value (.int answer), stack⟩ := by
  simpa only [Int.zero_add] using rangeSumFilteredWithin program (range n) 14 1 n 0 (by omega) rfl
    (fun i _ _ => ⟨14, _, by omega, tested n i⟩)
    (fun i lower upper => ⟨1, i, by omega, lower, by simp [range] at upper; omega,
      EvaluatesIn.lookup (by simp [range, ScalarEnv.set])⟩)
    n 0 0 (by omega) (by simp [range])

/-- Both branches execute on 0, 1, 2; only 0 and 2 enter the sum. -/
example : RuntimeCost.Reaches (step program) (charge .word program)
    ⟨.sumLoop (range 3) 0 0, []⟩ 79 ⟨.value (.int 2), []⟩ := by
  repeat first | exact RuntimeCost.Reaches.refl | runtime_step

example : RuntimeCost.Reaches (step program) (charge .word program)
    ⟨.sumLoop (range 0) 0 0, []⟩ 4 ⟨.value (.int 0), []⟩ := by
  repeat first | exact RuntimeCost.Reaches.refl | runtime_step

#print axioms rangeSumFilteredWithin
#print axioms EvaluatesIn.boolean_single
#print axioms bounded

end FilteredSumRuntimeRegression
