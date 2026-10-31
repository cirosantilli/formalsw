import lang.py.FormalSW.MachineMethodInvariant

/-! Statement entry and unpacking retain saved caller states for all modeled outcomes. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

variable (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
  (logicalAnchors physicalAnchors : Nat)

theorem step_unpack_preserves (value : Value) (names : List String) (following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .unpack names following env :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .unpack names following env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .unpack names following env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · apply protectGenerator_heap
    apply run_readonly_heap
    · exact fun outcome after executed => sequence_keeps_heap logical after value outcome executed
    · intro items _
      split <;> rfl
  · exact StateWithin.unpack module logical logicalAnchors layout.closed value names following env stack globals globalsInside inside
  · exact step_unpack_relocates module logical physical rename logicalAnchors physicalAnchors layout.runtime
      value names following env stack globals inside.1

theorem step_unpack_start_preserves (value : Value) (names : List String) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .unpackSequence names body otherwise following env :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .unpackSequence names body otherwise following env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .unpackSequence names body otherwise following env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · apply protectGenerator_heap
    apply run_readonly_heap
    · exact fun outcome after executed => sequence_keeps_heap logical after value outcome executed
    · intro items _; rfl
  · exact StateWithin.unpack_start module logical logicalAnchors value names body otherwise following env stack globals globalsInside inside
  · exact step_unpack_start_relocates module logical physical rename logicalAnchors physicalAnchors layout.runtime
      value names body otherwise following env stack globals inside.1

/-- Ordinary assignment evaluates its right-hand side before its supported targets. -/
theorem step_assignment (heap : Mutable.Heap) (anchors : Nat) (targets : List Expr) (value : Expr)
    (following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module anchors ⟨.block (.assign targets value :: following) env, stack, heap⟩ globals =
      match targets with
      | [target] => match target with
        | .name name => .next ⟨.expr value env, .assign name following env :: stack, heap⟩
        | .attribute base name => .next ⟨.expr value env, .assignAttribute base name following env :: stack, heap⟩
        | .subscript base (.slice lower upper stride) =>
            .next ⟨.expr value env, .assignSlice base (lower.getD (.constant .none))
              (upper.getD (.constant .none)) (stride.getD (.constant .none)) following env :: stack, heap⟩
        | .subscript base index => .next ⟨.expr value env, .assignItem base index following env :: stack, heap⟩
        | .tuple fields | .list fields => match Calls.targetNames fields with
          | some names => .next ⟨.expr value env, .unpack names following env :: stack, heap⟩
          | none => .unsupported
        | _ => .unsupported
      | _ => .unsupported := by
  cases targets with
  | nil => rfl
  | cons target targets =>
    cases targets with
    | cons next rest =>
      simp only [step]
      repeat' (first | simp_all | split)
    | nil =>
      cases target with
      | subscript base index => cases index <;> rfl
      | tuple fields | list fields =>
        cases read : Calls.targetNames fields <;> simp [step, read]
      | _ => rfl

theorem step_assignment_preserves (targets : List Expr) (value : Expr) (following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.block (.assign targets value :: following) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.assign targets value :: following) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.block (.assign targets value :: following) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have envInside := inside.1.1
  have bodyInside : ∀ statement ∈ following, StmtWithin logical.length statement :=
    fun statement member => inside.1.2 statement (List.mem_cons_of_mem _ member)
  have stackInside := inside.2
  simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step_assignment]
  repeat' split
  all_goals apply Preserves.unchanged layout
  all_goals first
    | rfl
    | trivial
    | (simp [StepWithin, StateWithin, WorkWithin, FrameWithin, envInside] <;> exact ⟨bodyInside, stackInside⟩)
    | simp [relocateStep, relocateState, relocateWork, relocateFrame]

end FormalSW.PyAst.HeapCalls.Relocation
