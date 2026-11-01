import lang.py.FormalSW.MachineMutationInvariant

/-! Read-only primitive dispatch composes with continuations that may mutate or allocate. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem run_readonly_preserves {α β : Type} (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (action : Mutable.Eval α) (otherAction : Mutable.Eval β)
    (move : α → β) (next : α → Mutable.Heap → Step State Mutable.Completion)
    (otherNext : β → Mutable.Heap → Step State Mutable.Completion)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (globalsInside : GlobalsWithin logical.length globals)
    (readonly : ∀ outcome after, action logical = some (outcome, after) → after = logical)
    (paired : otherAction physical = (action logical).map (fun pair => (pair.1.map move, physical)))
    (continues : ∀ value, action logical = some (.ok value, logical) →
      Preserves logical physical rename physicalAnchors (next value logical) (otherNext (move value) physical)) :
    Preserves logical physical rename physicalAnchors
      (run logicalAnchors logical action next globals)
      (run physicalAnchors physical otherAction otherNext (relocateGlobals rename globals)) := by
  cases executed : action logical with
  | none =>
    apply Preserves.unchanged layout <;>
      simp [run, executed, paired, StepHeap, StepWithin, relocateStep]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have same := readonly outcome after executed
    subst after
    cases outcome with
    | error exception =>
      simp only [run, executed, paired, Option.map_some, Except.map]
      apply Preserves.unchanged layout
      · rfl
      · exact ⟨globalsInside, by intro _ impossible; cases impossible⟩
      · rfl
    | ok value =>
      simpa only [run, executed, paired, Option.map_some, Except.map] using continues value executed

end FormalSW.PyAst.HeapCalls.Relocation
