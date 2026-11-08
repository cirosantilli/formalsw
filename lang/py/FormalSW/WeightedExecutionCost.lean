import lang.py.FormalSW.ExecutionCost

/-! Explicit weighted costs for deterministic execution traces. Charging is separate
from execution: it cannot change outcomes or turn unsupported code into a result. -/
namespace FormalSW.PyAst

inductive FinishesWith (step : σ → Step σ α) (charge : σ → Nat) :
    σ → Nat → Except ExceptionObject α → Prop where
  | done (h : step state = .done outcome) : FinishesWith step charge state (charge state) outcome
  | next (h : step state = .next following) (rest : FinishesWith step charge following cost outcome) :
      FinishesWith step charge state (charge state + cost) outcome

namespace FinishesWith

theorem finishes (h : FinishesWith step charge state cost outcome) : Finishes step state outcome := by
  induction h with
  | done h => exact .done h
  | next h _ ih => exact .next h ih

theorem unique (h : FinishesWith step charge state cost outcome)
    (other : FinishesWith step charge state otherCost otherOutcome) :
    cost = otherCost ∧ outcome = otherOutcome := by
  induction h generalizing otherCost otherOutcome with
  | done h =>
      cases other with
      | done h' => exact ⟨rfl, by simpa [h] using h'⟩
      | next h' _ => simp [h] at h'
  | next h _ ih =>
      cases other with
      | done h' => simp [h] at h'
      | next h' rest =>
          simp only [h, Step.next.injEq] at h'
          subst h'
          obtain ⟨same, result⟩ := ih rest
          exact ⟨congrArg (_ + ·) same, result⟩

/-- A potential increase is a lower bound on charged work, including terminal allocations. -/
theorem potential {step : σ → Step σ α} {charge : σ → Nat} (h : FinishesWith step charge state cost outcome)
    (volume : σ → Nat) (finalVolume : Except ExceptionObject α → Nat)
    (terminal : ∀ s result, step s = .done result → finalVolume result ≤ volume s + charge s)
    (transition : ∀ s next, step s = .next next → volume next ≤ volume s + charge s) :
    finalVolume outcome ≤ volume state + cost := by
  induction h with
  | done h => exact terminal _ _ h
  | next h _ ih => have := transition _ _ h; omega

end FinishesWith

theorem Finishes.exists_weighted_cost {step : σ → Step σ α} (h : Finishes step state outcome) (charge : σ → Nat) :
    ∃ cost, FinishesWith step charge state cost outcome := by
  induction h with
  | done h => exact ⟨_, .done h⟩
  | next h _ ih =>
      obtain ⟨cost, run⟩ := ih
      exact ⟨_, .next h run⟩

/-- Weighted finite prefixes compose without executing their continuation. -/
inductive ReachesWith (step : σ → Step σ α) (charge : σ → Nat) : σ → Nat → σ → Prop where
  | refl : ReachesWith step charge state 0 state
  | next (h : step state = .next following) (rest : ReachesWith step charge following cost final) :
      ReachesWith step charge state (charge state + cost) final

namespace ReachesWith

theorem trans (first : ReachesWith step charge a ca b) (second : ReachesWith step charge b cb c) :
    ReachesWith step charge a (ca + cb) c := by
  induction first with
  | refl => simpa using second
  | next h _ ih => simpa [Nat.add_assoc] using next h (ih second)

theorem finishes (first : ReachesWith step charge a ca b) (rest : FinishesWith step charge b cb result) :
    FinishesWith step charge a (ca + cb) result := by
  induction first with
  | refl => simpa using rest
  | next h _ ih => simpa [Nat.add_assoc] using FinishesWith.next h (ih rest)

end ReachesWith

namespace Execution

def WeightedTimeBound (execution : Execution α) (charge : execution.State → Nat) (bound : Nat) : Prop :=
  ∃ cost outcome, FinishesWith execution.step charge execution.initial cost outcome ∧ cost ≤ bound

theorem WeightedTimeBound.halts {execution : Execution α} {charge : execution.State → Nat}
    (h : execution.WeightedTimeBound charge bound) : execution.Halts := by
  obtain ⟨_, outcome, run, _⟩ := h
  exact ⟨outcome, run.finishes⟩

def WeightedBigO (family : ι → Execution α) (charge : ∀ input, (family input).State → Nat)
    (domain : ι → Prop) (size : ι → Nat) (bound : Nat → Nat) : Prop :=
  ∃ constant threshold : Nat, ∀ input, domain input → threshold ≤ size input →
    (family input).WeightedTimeBound (charge input) (constant * bound (size input))

end Execution
end FormalSW.PyAst
