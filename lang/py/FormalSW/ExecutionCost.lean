import lang.py.FormalSW.Execution

/-! Costs of actual execution traces, independent of the structural BigO classifier.
One transition (including the terminal transition) costs one unit. Operations hidden
inside a transition retain the underlying interpreter's abstraction; this is not
Python bit complexity or a wall-clock model. -/

namespace FormalSW.PyAst

/-- Exact transition count for a terminating execution, including its final step. -/
inductive FinishesIn (step : σ → Step σ α) : σ → Nat → Except ExceptionObject α → Prop where
  | done (h : step state = .done outcome) : FinishesIn step state 1 outcome
  | next (h : step state = .next following) (rest : FinishesIn step following cost outcome) :
      FinishesIn step state (cost + 1) outcome

namespace FinishesIn

theorem finishes (h : FinishesIn step state cost outcome) : Finishes step state outcome := by
  induction h with
  | done h => exact .done h
  | next h _ ih => exact .next h ih

theorem positive (h : FinishesIn step state cost outcome) : 0 < cost := by
  cases h <;> omega

/-- Determinism fixes both the result and the exact cost. -/
theorem unique (left : FinishesIn step state cost outcome)
    (right : FinishesIn step state cost' outcome') : cost = cost' ∧ outcome = outcome' := by
  induction left generalizing cost' outcome' with
  | done h =>
      cases right with
      | done h' => exact ⟨rfl, by simpa [h] using h'⟩
      | next h' _ => simp [h] at h'
  | next h _ ih =>
      cases right with
      | done h' => simp [h] at h'
      | next h' rest =>
          simp only [h, Step.next.injEq] at h'
          subst h'
          obtain ⟨costEq, resultEq⟩ := ih rest
          exact ⟨congrArg (· + 1) costEq, resultEq⟩

end FinishesIn

theorem Finishes.exists_cost (h : Finishes step state outcome) :
    ∃ cost, FinishesIn step state cost outcome := by
  induction h with
  | done h => exact ⟨1, .done h⟩
  | next h _ ih =>
      obtain ⟨cost, rest⟩ := ih
      exact ⟨cost + 1, .next h rest⟩

/-- Exact cost of a finite prefix, before its continuation runs. -/
inductive ReachesIn (step : σ → Step σ α) : σ → Nat → σ → Prop where
  | refl : ReachesIn step state 0 state
  | next (h : step state = .next following) (rest : ReachesIn step following cost final) :
      ReachesIn step state (cost + 1) final

namespace ReachesIn

theorem trans (h : ReachesIn step a first b) (rest : ReachesIn step b second c) :
    ReachesIn step a (first + second) c := by
  induction h with
  | refl => simpa using rest
  | next h _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next h (ih rest)

theorem finishes (h : ReachesIn step a prefixCost b) (rest : FinishesIn step b cost outcome) :
    FinishesIn step a (prefixCost + cost) outcome := by
  induction h with
  | refl => simpa using rest
  | next h _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using FinishesIn.next h (ih rest)

end ReachesIn

namespace Execution

/-- A successful or exceptional result is reached within the stated number of transitions.
Unsupported states and exhausted observation fuel do not establish this property. -/
def TimeBound (execution : Execution α) (bound : Nat) : Prop :=
  ∃ cost outcome, FinishesIn execution.step execution.initial cost outcome ∧ cost ≤ bound

theorem TimeBound.halts {execution : Execution α} (h : execution.TimeBound bound) : execution.Halts := by
  obtain ⟨_, outcome, finished, _⟩ := h
  exact ⟨outcome, finished.finishes⟩

theorem TimeBound.mono {execution : Execution α} (h : execution.TimeBound small) (hle : small ≤ large) :
    execution.TimeBound large := by
  obtain ⟨cost, outcome, finished, bounded⟩ := h
  exact ⟨cost, outcome, finished, Nat.le_trans bounded hle⟩

/-- A size map can depend on several arguments; the bound is uniform over all
inputs of that size satisfying the domain predicate. -/
def IsBigO (family : ι → Execution α) (domain : ι → Prop)
    (size : ι → Nat) (bound : Nat → Nat) : Prop :=
  ∃ constant threshold : Nat, ∀ input, domain input → threshold ≤ size input →
    (family input).TimeBound (constant * bound (size input))

/-- A pointwise cost bound gives an asymptotic bound without a shape classifier. -/
theorem isBigO_of_timeBound (family : ι → Execution α) (domain : ι → Prop)
    (size : ι → Nat) (cost bound : Nat → Nat)
    (executed : ∀ input, domain input → (family input).TimeBound (cost (size input)))
    (asymptotic : Growth.IsBigO cost bound) : IsBigO family domain size bound := by
  obtain ⟨constant, threshold, bounded⟩ := asymptotic
  exact ⟨constant, threshold, fun input valid large =>
    (executed input valid).mono (bounded _ large)⟩

/-- Successful finite observation supplies a cost bound, never a fallback result. -/
theorem timeBound_of_observeFrom {step : σ → Step σ α} {state : σ}
    (h : observeFrom step fuel state = .done outcome) :
    ∃ cost, FinishesIn step state cost outcome ∧ cost ≤ fuel := by
  induction fuel generalizing state with
  | zero => simp [observeFrom] at h
  | succ fuel ih =>
      cases next : step state with
      | next following =>
          obtain ⟨cost, run, bounded⟩ := ih (by simpa [observeFrom, next] using h)
          exact ⟨cost + 1, .next next run, by omega⟩
      | done result =>
          simp only [observeFrom, next, Observation.done.injEq] at h
          subst result
          exact ⟨1, .done next, by omega⟩
      | unsupported => simp [observeFrom, next] at h

theorem timeBound_of_observe {execution : Execution α}
    (h : execution.observe fuel = .done outcome) : execution.TimeBound fuel := by
  obtain ⟨cost, run, bounded⟩ := timeBound_of_observeFrom h
  exact ⟨cost, outcome, run, bounded⟩

end Execution
end FormalSW.PyAst
