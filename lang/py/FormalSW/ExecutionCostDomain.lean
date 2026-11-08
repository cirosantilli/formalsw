import lang.py.FormalSW.ExecutionCost

namespace FormalSW.PyAst.Execution

/-- Restrict a complexity bound to inputs which eventually satisfy its domain. -/
theorem IsBigO.of_eventual_domain {family : ι → Execution α}
    {domain restricted : ι → Prop} {size : ι → Nat} {bound : Nat → Nat}
    (bounded : IsBigO family domain size bound) (threshold : Nat)
    (valid : ∀ input, restricted input → threshold ≤ size input → domain input) :
    IsBigO family restricted size bound := by
  obtain ⟨constant, cutoff, run⟩ := bounded
  refine ⟨constant, max cutoff threshold, fun input allowed large => ?_⟩
  exact run input (valid input allowed (Nat.le_trans (Nat.le_max_right _ _) large))
    (Nat.le_trans (Nat.le_max_left _ _) large)

end FormalSW.PyAst.Execution
