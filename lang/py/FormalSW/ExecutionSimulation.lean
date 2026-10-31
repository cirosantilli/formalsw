import lang.py.FormalSW.Execution

/-! Relational execution proofs preserve termination, supported divergence, and unsupported code. -/
namespace FormalSW.PyAst
set_option Elab.async false

namespace Step

/-- Matching transitions may relate different state and result types. -/
inductive Relates (states : σ → τ → Prop)
    (outcomes : Except ExceptionObject α → Except ExceptionObject β → Prop) :
    Step σ α → Step τ β → Prop where
  | next {left : σ} {right : τ} (related : states left right) : Relates states outcomes (.next left) (.next right)
  | done {left : Except ExceptionObject α} {right : Except ExceptionObject β} (related : outcomes left right) : Relates states outcomes (.done left) (.done right)
  | unsupported : Relates states outcomes .unsupported .unsupported

theorem Relates.flip {states : σ → τ → Prop}
    {outcomes : Except ExceptionObject α → Except ExceptionObject β → Prop}
    {left : Step σ α} {right : Step τ β} (related : Relates states outcomes left right) :
    Relates (fun right left => states left right) (fun right left => outcomes left right) right left := by
  cases related with
  | next related => exact .next related
  | done related => exact .done related
  | unsupported => exact .unsupported

theorem Relates.next_inv {states : σ → τ → Prop}
    {outcomes : Except ExceptionObject α → Except ExceptionObject β → Prop}
    {a : σ} {b : Step τ β} (related : Relates states outcomes (.next a) b) :
    ∃ following, b = .next following ∧ states a following := by
  cases related with
  | next related => exact ⟨_, rfl, related⟩

theorem Relates.done_inv {states : σ → τ → Prop}
    {outcomes : Except ExceptionObject α → Except ExceptionObject β → Prop}
    {a : Except ExceptionObject α} {b : Step τ β} (related : Relates states outcomes (.done a) b) :
    ∃ result, b = .done result ∧ outcomes a result := by
  cases related with
  | done related => exact ⟨_, rfl, related⟩

theorem Relates.unsupported_inv {states : σ → τ → Prop}
    {outcomes : Except ExceptionObject α → Except ExceptionObject β → Prop}
    {b : Step τ β} (related : Relates states outcomes .unsupported b) : b = .unsupported := by
  cases related
  rfl

def map (state : σ → τ) (result : α → β) : Step σ α → Step τ β
  | .next following => .next (state following)
  | .done outcome => .done (outcome.map result)
  | .unsupported => .unsupported

theorem Relates.map (state : σ → τ) (result : α → β) (transition : Step σ α) :
    Relates (fun a b => a = state b) (fun a b => a = b.map result) (transition.map state result) transition := by
  cases transition with
  | next following => exact .next rfl
  | done outcome => exact .done rfl
  | unsupported => exact .unsupported

theorem Relates.trans {states : σ → τ → Prop} {moreStates : τ → υ → Prop}
    {outcomes : Except ExceptionObject α → Except ExceptionObject β → Prop}
    {moreOutcomes : Except ExceptionObject β → Except ExceptionObject γ → Prop}
    {a : Step σ α} {b : Step τ β} {c : Step υ γ}
    (first : Relates states outcomes a b) (second : Relates moreStates moreOutcomes b c) :
    Relates (fun a c => ∃ b, states a b ∧ moreStates b c)
      (fun a c => ∃ b, outcomes a b ∧ moreOutcomes b c) a c := by
  cases first <;> cases second
  · exact .next ⟨_, ‹states _ _›, ‹moreStates _ _›⟩
  · exact .done ⟨_, ‹outcomes _ _›, ‹moreOutcomes _ _›⟩
  · exact .unsupported

end Step

namespace Execution

/-- One interpreter step corresponds to one step. The state relation may carry
an address map that changes after allocation; no single global map is required. -/
structure Bisimulation (left : Execution α) (right : Execution β)
    (states : left.State → right.State → Prop)
    (outcomes : Except ExceptionObject α → Except ExceptionObject β → Prop) : Prop where
  initial : states left.initial right.initial
  transition : ∀ a b, states a b → Step.Relates states outcomes (left.step a) (right.step b)

variable {left : Execution α} {right : Execution β}
  {states : left.State → right.State → Prop}
  {outcomes : Except ExceptionObject α → Except ExceptionObject β → Prop}

theorem Bisimulation.flip (paired : Bisimulation left right states outcomes) :
    Bisimulation right left (fun b a => states a b) (fun b a => outcomes a b) :=
  ⟨paired.initial, fun b a related => (paired.transition a b related).flip⟩

/-- A symbolic interpreter trace can be encoded into the actual source machine. -/
theorem Bisimulation.of_encoding (left : Execution α) (right : Execution β)
    (encode : right.State → left.State) (result : β → α)
    (initial : left.initial = encode right.initial)
    (transition : ∀ state, left.step (encode state) = (right.step state).map encode result) :
    Bisimulation left right (fun a b => a = encode b) (fun a b => a = b.map result) := by
  refine ⟨initial, ?_⟩
  rintro a b rfl
  rw [transition]
  exact Step.Relates.map encode result (right.step b)

theorem Bisimulation.trans {middle : Execution β} {last : Execution γ}
    {moreStates : middle.State → last.State → Prop}
    {moreOutcomes : Except ExceptionObject β → Except ExceptionObject γ → Prop}
    {firstStates : left.State → middle.State → Prop}
    {firstOutcomes : Except ExceptionObject α → Except ExceptionObject β → Prop}
    (first : Bisimulation left middle firstStates firstOutcomes)
    (second : Bisimulation middle last moreStates moreOutcomes) :
    Bisimulation left last (fun a c => ∃ b, firstStates a b ∧ moreStates b c)
      (fun a c => ∃ b, firstOutcomes a b ∧ moreOutcomes b c) := by
  refine ⟨⟨middle.initial, first.initial, second.initial⟩, ?_⟩
  rintro a c ⟨b, firstRelated, secondRelated⟩
  exact (first.transition a b firstRelated).trans (second.transition b c secondRelated)

/-- Transport a finite derivation, retaining the relation on its actual final outcome. -/
theorem Bisimulation.finishes_from (paired : Bisimulation left right states outcomes)
    {a : left.State} {b : right.State} {outcome : Except ExceptionObject α}
    (related : states a b) (finished : Finishes left.step a outcome) :
    ∃ result, outcomes outcome result ∧ Finishes right.step b result := by
  induction finished generalizing b with
  | done transition =>
    have matched := paired.transition _ b related
    rw [transition] at matched
    obtain ⟨result, transition, resultRelated⟩ := matched.done_inv
    exact ⟨result, resultRelated, .done transition⟩
  | next transition _ ih =>
    have matched := paired.transition _ b related
    rw [transition] at matched
    obtain ⟨following, next, nextRelated⟩ := matched.next_inv
    obtain ⟨result, resultRelated, finished⟩ := ih nextRelated
    exact ⟨result, resultRelated, .next next finished⟩

theorem Bisimulation.finishes (paired : Bisimulation left right states outcomes)
    {outcome : Except ExceptionObject α} (finished : Finishes left.step left.initial outcome) :
    ∃ result, outcomes outcome result ∧ Finishes right.step right.initial result :=
  paired.finishes_from paired.initial finished

/-- Image the infinite-run invariant through the state relation. Unsupported
transitions cannot witness a next step and therefore cannot establish divergence. -/
theorem Bisimulation.diverges (paired : Bisimulation left right states outcomes)
    (diverges : left.Diverges) : right.Diverges := by
  obtain ⟨invariant, initial, closed⟩ := diverges
  refine ⟨fun b => ∃ a, invariant a ∧ states a b, ⟨left.initial, initial, paired.initial⟩, ?_⟩
  rintro b ⟨a, valid, related⟩
  obtain ⟨following, transition, preserved⟩ := closed a valid
  have matched := paired.transition a b related
  rw [transition] at matched
  obtain ⟨other, next, nextRelated⟩ := matched.next_inv
  exact ⟨other, next, following, preserved, nextRelated⟩

theorem Bisimulation.diverges_iff (paired : Bisimulation left right states outcomes) :
    left.Diverges ↔ right.Diverges :=
  ⟨paired.diverges, paired.flip.diverges⟩

theorem Bisimulation.halts_iff (paired : Bisimulation left right states outcomes) :
    left.Halts ↔ right.Halts := by
  constructor
  · rintro ⟨outcome, finished⟩
    obtain ⟨result, _, transported⟩ := paired.finishes finished
    exact ⟨result, transported⟩
  · rintro ⟨outcome, finished⟩
    obtain ⟨result, _, transported⟩ := paired.flip.finishes finished
    exact ⟨result, transported⟩

namespace Observation

inductive Relates (outcomes : Except ExceptionObject α → Except ExceptionObject β → Prop) :
    Observation α → Observation β → Prop where
  | pending : Relates outcomes .pending .pending
  | unsupported : Relates outcomes .unsupported .unsupported
  | done {left : Except ExceptionObject α} {right : Except ExceptionObject β} (related : outcomes left right) : Relates outcomes (.done left) (.done right)

theorem Relates.unsupported_iff {outcomes : Except ExceptionObject α → Except ExceptionObject β → Prop}
    {a : Observation α} {b : Observation β} (related : Relates outcomes a b) :
    a = .unsupported ↔ b = .unsupported := by
  cases related <;> simp

end Observation

/-- Every observation length is covered, rather than a chosen execution cutoff. -/
theorem Bisimulation.observe_from (paired : Bisimulation left right states outcomes)
    (fuel : Nat) {a : left.State} {b : right.State} (related : states a b) :
    Observation.Relates outcomes (observeFrom left.step fuel a) (observeFrom right.step fuel b) := by
  induction fuel generalizing a b with
  | zero => exact .pending
  | succ fuel ih =>
    have matched := paired.transition a b related
    cases first : left.step a with
    | next following =>
      rw [first] at matched
      obtain ⟨other, next, nextRelated⟩ := matched.next_inv
      simpa only [observeFrom, first, next] using ih nextRelated
    | done result =>
      rw [first] at matched
      obtain ⟨other, next, resultRelated⟩ := matched.done_inv
      simp only [observeFrom, first, next]
      exact .done resultRelated
    | unsupported =>
      rw [first] at matched
      simp only [observeFrom, first, matched.unsupported_inv]
      exact .unsupported

theorem Bisimulation.observe (paired : Bisimulation left right states outcomes) (fuel : Nat) :
    Observation.Relates outcomes (left.observe fuel) (right.observe fuel) :=
  paired.observe_from fuel paired.initial

theorem Bisimulation.supported_iff (paired : Bisimulation left right states outcomes) :
    left.Supported ↔ right.Supported := by
  constructor
  · intro supported fuel unsupported
    exact supported fuel ((paired.observe fuel).unsupported_iff.mpr unsupported)
  · intro supported fuel unsupported
    exact supported fuel ((paired.observe fuel).unsupported_iff.mp unsupported)

theorem Bisimulation.equiv {left right : Execution α} {states : left.State → right.State → Prop}
    (paired : Bisimulation left right states Eq) : left.Equiv right := by
  intro outcome
  constructor
  · intro finished
    obtain ⟨result, equal, transported⟩ := paired.finishes finished
    simpa only [← equal] using transported
  · intro finished
    obtain ⟨result, equal, transported⟩ := paired.flip.finishes finished
    simpa only [equal] using transported

end Execution
end FormalSW.PyAst
