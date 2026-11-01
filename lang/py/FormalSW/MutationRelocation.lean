import lang.py.FormalSW.SequenceRelocation

/-! Relating mutations that retain the heap's object count and address map.
Unsupported evaluations match too; exception exits retain intermediate writes. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

def MutationRelocates {α β : Type} (logical physical : Heap) (rename : Nat → Nat)
    (convert : α → β) (action : Eval α) (otherAction : Eval β) : Prop :=
  match action logical with
  | none => otherAction physical = none
  | some (outcome, after) => ∃ other,
      otherAction physical = some (outcome.map convert, other) ∧
      ExecutionLayout after other rename ∧
      after.length = logical.length ∧ other.length = physical.length

variable {α β γ δ : Type} {logical physical : Heap} {rename : Nat → Nat}

theorem MutationRelocates.completed {convert : α → β} {action : Eval α} {otherAction : Eval β}
    (related : MutationRelocates logical physical rename convert action otherAction)
    (outcome : Except ExceptionObject α) (after : Heap) (executed : action logical = some (outcome, after)) :
    ∃ other, otherAction physical = some (outcome.map convert, other) ∧
      ExecutionLayout after other rename ∧ after.length = logical.length ∧ other.length = physical.length := by
  simpa only [MutationRelocates, executed] using related

theorem MutationRelocates.unsupported_iff {convert : α → β} {action : Eval α} {otherAction : Eval β}
    (related : MutationRelocates logical physical rename convert action otherAction) :
    action logical = none ↔ otherAction physical = none := by
  cases ran : action logical with
  | none => simpa only [MutationRelocates, ran, true_iff] using related
  | some pair =>
    obtain ⟨other, paired, _⟩ := related.completed pair.1 pair.2 ran
    simp [paired]

theorem MutationRelocates.pure (layout : ExecutionLayout logical physical rename)
    (convert : α → β) (value : α) :
    MutationRelocates logical physical rename convert (pure value) (pure (convert value)) :=
  ⟨physical, rfl, layout, rfl, rfl⟩

theorem MutationRelocates.error (layout : ExecutionLayout logical physical rename)
    (convert : α → β) (name : String) :
    MutationRelocates logical physical rename convert (error name) (error name) :=
  ⟨physical, rfl, layout, rfl, rfl⟩

theorem MutationRelocates.readonly (layout : ExecutionLayout logical physical rename)
    (convert : α → β) (action : Eval α) (otherAction : Eval β)
    (paired : otherAction physical = (action logical).map (fun pair => (pair.1.map convert, physical)))
    (stationary : ∀ outcome after, action logical = some (outcome, after) → after = logical) :
    MutationRelocates logical physical rename convert action otherAction := by
  unfold MutationRelocates
  cases ran : action logical with
  | none => simpa [ran] using paired
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    obtain rfl := stationary outcome after ran
    exact ⟨physical, by simpa [ran] using paired, layout, rfl, rfl⟩

theorem MutationRelocates.bind (convert : α → β) (finish : γ → δ)
    (action : Eval α) (otherAction : Eval β) (next : α → Eval γ) (otherNext : β → Eval δ)
    (first : MutationRelocates logical physical rename convert action otherAction)
    (following : ∀ value middle other,
      action logical = some (.ok value, middle) →
      ExecutionLayout middle other rename → middle.length = logical.length → other.length = physical.length →
      MutationRelocates middle other rename finish (next value) (otherNext (convert value))) :
    MutationRelocates logical physical rename finish (action >>= next) (otherAction >>= otherNext) := by
  unfold MutationRelocates at first ⊢
  cases ran : action logical with
  | none =>
    simp only [ran] at first
    simp [eval_bind, ran, first]
  | some pair =>
    rcases pair with ⟨outcome, middle⟩
    simp only [ran] at first
    obtain ⟨other, paired, layout, leftLength, rightLength⟩ := first
    cases outcome with
    | error exception =>
      simp only [eval_bind, ran, Option.bind_eq_bind, Option.bind_some, paired, Except.map]
      exact ⟨other, rfl, layout, leftLength, rightLength⟩
    | ok value =>
      have rest := following value middle other ran layout leftLength rightLength
      unfold MutationRelocates at rest
      simp only [eval_bind, ran, Option.bind_eq_bind, Option.bind_some, paired, Except.map]
      cases continued : next value middle with
      | none => simpa [continued] using rest
      | some pair =>
        rcases pair with ⟨result, after⟩
        simp only [continued] at rest ⊢
        obtain ⟨last, finished, retained, left, right⟩ := rest
        exact ⟨last, finished, retained, left.trans leftLength, right.trans rightLength⟩

theorem MutationRelocates.readonly_bind (layout : ExecutionLayout logical physical rename)
    (convert : α → β) (finish : γ → δ) (action : Eval α) (otherAction : Eval β)
    (next : α → Eval γ) (otherNext : β → Eval δ)
    (paired : otherAction physical = (action logical).map (fun pair => (pair.1.map convert, physical)))
    (stationary : ∀ outcome after, action logical = some (outcome, after) → after = logical)
    (following : ∀ value, action logical = some (.ok value, logical) →
      MutationRelocates logical physical rename finish (next value) (otherNext (convert value))) :
    MutationRelocates logical physical rename finish (action >>= next) (otherAction >>= otherNext) := by
  unfold MutationRelocates
  cases ran : action logical with
  | none => simp [eval_bind, ran, paired]
  | some pair =>
    rcases pair with ⟨outcome, middle⟩
    obtain rfl := stationary outcome middle ran
    cases outcome with
    | error exception =>
      simp only [eval_bind, paired, ran, Option.map_some, Except.map, Option.bind_eq_bind, Option.bind_some]
      exact ⟨physical, rfl, layout, trivial, rfl⟩
    | ok value =>
      simpa only [MutationRelocates, eval_bind, paired, ran, Option.map_some, Except.map,
        Option.bind_eq_bind, Option.bind_some] using following value ran

end FormalSW.PyAst.Mutable.Relocation
