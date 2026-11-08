import lang.py.FormalSW.WeightedExecutionCost

/-! Runtime-cost derivations require a cost rule for every executed state.
An absent rule cannot silently become a unit-cost operation. The transition
relation remains the source interpreter's relation, including exceptions. -/
namespace FormalSW.PyAst.RuntimeCost

inductive Finishes (step : σ → Step σ α) (charge : σ → Option Nat) :
    σ → Nat → Except ExceptionObject α → Prop where
  | done (transition : step state = .done outcome) (measured : charge state = some amount) :
      Finishes step charge state amount outcome
  | next (transition : step state = .next following) (measured : charge state = some amount)
      (rest : Finishes step charge following cost outcome) :
      Finishes step charge state (amount + cost) outcome

namespace Finishes

theorem execution (run : Finishes step charge state cost outcome) :
    PyAst.Finishes step state outcome := by
  induction run with
  | done transition _ => exact .done transition
  | next transition _ _ ih => exact .next transition ih

theorem weighted (run : Finishes step charge state cost outcome) :
    FinishesWith step (fun state => (charge state).getD 0) state cost outcome := by
  induction run with
  | done transition measured =>
      simpa only [measured, Option.getD_some] using
        (FinishesWith.done (charge := fun state => (charge state).getD 0) transition)
  | next transition measured _ ih =>
      simpa only [measured, Option.getD_some] using FinishesWith.next transition ih

theorem unique (run : Finishes step charge state cost outcome)
    (other : Finishes step charge state otherCost otherOutcome) :
    cost = otherCost ∧ outcome = otherOutcome := run.weighted.unique other.weighted

theorem measured (run : Finishes step charge state cost outcome) :
    ∃ amount, charge state = some amount := by
  cases run with
  | done _ measured => exact ⟨_, measured⟩
  | next _ measured _ => exact ⟨_, measured⟩

theorem impossible_of_missing (missing : charge state = none) :
    ¬ Finishes step charge state cost outcome := by
  intro run
  obtain ⟨_, measured⟩ := run.measured
  simp [missing] at measured

end Finishes

inductive Reaches (step : σ → Step σ α) (charge : σ → Option Nat) : σ → Nat → σ → Prop where
  | refl : Reaches step charge state 0 state
  | next (transition : step state = .next following) (measured : charge state = some amount)
      (rest : Reaches step charge following cost final) :
      Reaches step charge state (amount + cost) final

namespace Reaches

/-- Consume a known budget without guessing the cost of the remaining trace. -/
theorem next_budget (transition : step state = .next following)
    (covered : charge state = some ((charge state).getD 0))
    (enough : (charge state).getD 0 ≤ budget)
    (rest : Reaches step charge following (budget - (charge state).getD 0) final) :
    Reaches step charge state budget final := by
  have run := next transition covered rest
  simpa only [Nat.add_sub_of_le enough] using run

theorem trans (first : Reaches step charge a ca b) (second : Reaches step charge b cb c) :
    Reaches step charge a (ca + cb) c := by
  induction first with
  | refl => simpa using second
  | next transition measured _ ih =>
      simpa [Nat.add_assoc] using next transition measured (ih second)

theorem finishes (first : Reaches step charge a ca b) (rest : Finishes step charge b cb result) :
    Finishes step charge a (ca + cb) result := by
  induction first with
  | refl => simpa using rest
  | next transition measured _ ih =>
      simpa [Nat.add_assoc] using Finishes.next transition measured (ih rest)

end Reaches

def TimeBound (execution : Execution α) (charge : execution.State → Option Nat) (bound : Nat) : Prop :=
  ∃ cost outcome, Finishes execution.step charge execution.initial cost outcome ∧ cost ≤ bound

theorem TimeBound.halts {execution : Execution α} {charge : execution.State → Option Nat}
    (bounded : TimeBound execution charge bound) : execution.Halts := by
  obtain ⟨_, outcome, run, _⟩ := bounded
  exact ⟨outcome, run.execution⟩

theorem TimeBound.mono {execution : Execution α} {charge : execution.State → Option Nat}
    (bounded : TimeBound execution charge small) (larger : small ≤ large) :
    TimeBound execution charge large := by
  obtain ⟨cost, outcome, run, upper⟩ := bounded
  exact ⟨cost, outcome, run, Nat.le_trans upper larger⟩

/-- A single bound, uniform over all valid inputs of each size, with no missing cost rules. -/
def IsBigO (family : ι → Execution α) (charge : ∀ input, (family input).State → Option Nat)
    (domain : ι → Prop) (size : ι → Nat) (bound : Nat → Nat) : Prop :=
  ∃ constant threshold : Nat, ∀ input, domain input → threshold ≤ size input →
    TimeBound (family input) (charge input) (constant * bound (size input))

end FormalSW.PyAst.RuntimeCost

/-- Advance only when the source transition and charge reduce, consuming a finite budget. -/
macro "runtime_step" : tactic => `(tactic|
  (apply FormalSW.PyAst.RuntimeCost.Reaches.next_budget
   next => rfl
   next => rfl
   next => exact of_decide_eq_true rfl))
