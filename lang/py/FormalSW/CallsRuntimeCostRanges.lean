import lang.py.FormalSW.CallsRuntimeCostControl

namespace FormalSW.PyAst.Calls.Runtime

/-- An invariant bounds both each range guard and each actual source iteration.
The arithmetic policy is explicit, so this rule also supports bit-cost loops. -/
theorem rangeLoopWithin (arithmetic : PrimitiveWork.Arithmetic) (module : Module)
    (name : String) (body following : List Stmt) (stop : Int)
    (invariant : Int → ScalarEnv → Prop) (guardBound iterationBound : Nat)
    (guard : ∀ i env, invariant i env → rangeWork arithmetic i stop 1 ≤ guardBound)
    (iteration : ∀ i env, i < stop → invariant i env → ∀ stack,
      ∃ cost env', invariant (i + 1) env' ∧
        RuntimeCost.Reaches (step module) (charge arithmetic module)
          ⟨.block (body ++ [loopContinuation body
            (.rangeStepLoop name (i + 1) stop 1 body [])] ++ following)
            (env.set name (.int i)), stack⟩ cost
          ⟨.block (.rangeStepLoop name (i + 1) stop 1 body [] :: following) env', stack⟩ ∧
        cost ≤ iterationBound)
    (remaining : Nat) (start : Int) (env : ScalarEnv)
    (endpoint : stop = start + remaining) (valid : invariant start env) (stack : List Frame) :
    ∃ cost env', invariant stop env' ∧
      RuntimeCost.Reaches (step module) (charge arithmetic module)
        ⟨.block (.rangeStepLoop name start stop 1 body [] :: following) env, stack⟩ cost
        ⟨.block following env', stack⟩ ∧
      cost ≤ (iterationBound + guardBound) * remaining + guardBound := by
  induction remaining generalizing start env with
  | zero =>
      have eq : stop = start := by simpa using endpoint
      refine ⟨rangeWork arithmetic start stop 1, env, eq ▸ valid, ?_, ?_⟩
      · apply RuntimeCost.Reaches.next (amount := rangeWork arithmetic start stop 1) (cost := 0)
          (following := ⟨.block following env, stack⟩)
        · simp [step, rangeContinues, eq]
        · rfl
        · exact .refl
      · simpa using guard start env valid
  | succ remaining ih =>
      have active : start < stop := by omega
      obtain ⟨bodyCost, env', valid', run, bodyBound⟩ := iteration start env active valid stack
      obtain ⟨tailCost, final, validFinal, tail, tailBound⟩ := ih (start + 1) env' (by omega) valid'
      refine ⟨rangeWork arithmetic start stop 1 + (bodyCost + tailCost), final, validFinal, ?_, ?_⟩
      · apply RuntimeCost.Reaches.next
          (amount := rangeWork arithmetic start stop 1) (cost := bodyCost + tailCost)
          (following := ⟨.block (body ++ [loopContinuation body
            (.rangeStepLoop name (start + 1) stop 1 body [])] ++ following)
            (env.set name (.int start)), stack⟩)
        · simp [step, rangeContinues, active]
        · rfl
        · exact run.trans tail
      · have headBound := guard start env valid
        rw [Nat.mul_succ]
        omega

end FormalSW.PyAst.Calls.Runtime
