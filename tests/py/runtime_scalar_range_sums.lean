import lang.py.FormalSW.CallsRuntimeCostFunctions

namespace ScalarRangeSumRuntimeRegression
open FormalSW.PyAst Calls Calls.Runtime

private def program : Module :=
  { body := [.functionDef "identity" [⟨"x", none, none⟩] none [.return (.name "x")]] }

private theorem identity_cost (k : Int) :
    ReturnsIn .word program "identity" [.int k] 4 (.int k) := by
  intro stack
  repeat first | exact RuntimeCost.Reaches.refl | runtime_step

private def element : Expr := .ifExp
  (.compare (.name "k") [(.lt, .constant (.int 0))])
  (.constant (.int 7)) (.call (.name "identity") [.name "k"])

/-- Only the selected branch executes: the constant branch costs 10, the call 16. -/
private theorem item_cost (k : Int) (env : ScalarEnv) (lookup : env "k" = some (.int k)) :
    ∃ cost value, cost ≤ 16 ∧ EvaluatesIn .word program env element cost (.int value) := by
  have tested : EvaluatesIn .word program env
      (.compare (.name "k") [(.lt, .constant (.int 0))]) 7 (.bool (decide (k < 0))) :=
    EvaluatesIn.compare (EvaluatesIn.lookup lookup) EvaluatesIn.constant
      (by simp [scalarCompare, evalCmpOp])
  by_cases negative : k < 0
  · refine ⟨10, 7, by decide, ?_⟩
    apply EvaluatesIn.conditional (cb := 1) tested
    simpa [negative] using (EvaluatesIn.constant (value := .int 7))
  · refine ⟨16, k, by decide, ?_⟩
    apply EvaluatesIn.conditional (cb := 7) tested
    simpa [negative] using EvaluatesIn.call_single (EvaluatesIn.lookup lookup) (identity_cost k)

/-- Signed starts, empty ranges and branch changes retain both traversal bounds. -/
example (start : Int) (count : Nat) (env : ScalarEnv) (stack : List Frame) :
    ∃ cost answer, 13 * count + 4 ≤ cost ∧ cost ≤ 29 * count + 4 ∧
      RuntimeCost.Reaches (step program) (charge .word program)
        ⟨.sumLoop ⟨"k", element, [], start + count, 1, env⟩ start 0, stack⟩ cost
        ⟨.value (.int answer), stack⟩ :=
  rangeSumWithin program _ 16 rfl rfl
    (fun k => item_cost k _ (by simp [ScalarEnv.set])) count start 0 rfl stack

end ScalarRangeSumRuntimeRegression
