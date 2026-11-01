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

theorem unpacking_assignment_within (bound : Nat) (targets : List Expr) (value : Expr) :
    ∀ statement ∈ UnpackingTargets.assignment targets value, StmtWithin bound statement :=
  UnpackingTargets.lower_forall (StmtWithin bound)
    (fun _ _ => by simp [StmtWithin]) (fun _ => by simp [StmtWithin]) _ _ _

theorem relocate_unpacking_assignment (targets : List Expr) (value : Expr) :
    (UnpackingTargets.assignment targets value).map (relocateStmt rename) =
      UnpackingTargets.assignment targets value := by
  have fixed : ∀ statement ∈ UnpackingTargets.assignment targets value,
      relocateStmt rename statement = statement :=
    UnpackingTargets.lower_forall (fun statement => relocateStmt rename statement = statement)
      (fun _ _ => by simp [relocateStmt]) (fun _ => by simp [relocateStmt]) _ _ _
  calc
    (UnpackingTargets.assignment targets value).map (relocateStmt rename) =
        (UnpackingTargets.assignment targets value).map id := List.map_congr_left fixed
    _ = _ := List.map_id _

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
          | none => .next ⟨.block (UnpackingTargets.assignment fields value ++ following) env, stack, heap⟩
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
    | (refine ⟨⟨envInside, ?_⟩, stackInside⟩
       intro statement member
       rcases List.mem_append.mp member with member | member
       · exact unpacking_assignment_within _ _ _ statement member
       · exact bodyInside statement member)
    | simp [relocateStep, relocateState, relocateWork, relocateFrame, relocate_unpacking_assignment]

/-- Function-local annotations do not evaluate their annotation expressions. -/
theorem step_annotation (heap : Mutable.Heap) (anchors : Nat) (target annotation : Expr) (value : Option Expr)
    (following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module anchors ⟨.block (.annAssign target annotation value :: following) env, stack, heap⟩ globals =
      match target, value with
      | .name name, some expression => .next ⟨.expr expression env, .assign name following env :: stack, heap⟩
      | .name _, none => .next ⟨.block following env, stack, heap⟩
      | .attribute base name, some expression =>
          .next ⟨.expr expression env, .assignAttribute base name following env :: stack, heap⟩
      | .attribute base _, none => .next ⟨.expr base env, .discard following env :: stack, heap⟩
      | _, _ => .unsupported := by
  cases target <;> cases value <;> rfl

theorem step_annotation_preserves (target annotation : Expr) (value : Option Expr) (following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.block (.annAssign target annotation value :: following) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.annAssign target annotation value :: following) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.block (.annAssign target annotation value :: following) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have envInside := inside.1.1
  have bodyInside : ∀ statement ∈ following, StmtWithin logical.length statement :=
    fun statement member => inside.1.2 statement (List.mem_cons_of_mem _ member)
  have stackInside := inside.2
  simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step_annotation]
  repeat' split
  all_goals apply Preserves.unchanged layout
  all_goals first
    | rfl
    | trivial
    | (simp [StepWithin, StateWithin, WorkWithin, FrameWithin, envInside] <;> exact ⟨bodyInside, stackInside⟩)
    | simp [relocateStep, relocateState, relocateWork, relocateFrame]

/-- Augmented assignment saves its target before evaluating the right operand. -/
theorem step_augmented_assignment (heap : Mutable.Heap) (anchors : Nat) (target : Expr) (op : BinOp) (right : Expr)
    (following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module anchors ⟨.block (.augAssign target op right :: following) env, stack, heap⟩ globals =
      match target with
      | .name name =>
          .next ⟨.expr (.name name) env, .binaryLeft op right env true :: .assign name following env :: stack, heap⟩
      | .attribute base name => .next ⟨.expr base env, .augmentAttribute name op right following env :: stack, heap⟩
      | .subscript _ (.slice _ _ _) => .unsupported
      | .subscript base index => .next ⟨.expr base env, .augmentItemReceiver index op right following env :: stack, heap⟩
      | _ => .unsupported := by
  cases target with
  | subscript base index => cases index <;> rfl
  | _ => rfl

theorem step_augmented_assignment_preserves (target : Expr) (op : BinOp) (right : Expr) (following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.block (.augAssign target op right :: following) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.augAssign target op right :: following) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.block (.augAssign target op right :: following) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have envInside := inside.1.1
  have bodyInside : ∀ statement ∈ following, StmtWithin logical.length statement :=
    fun statement member => inside.1.2 statement (List.mem_cons_of_mem _ member)
  have stackInside := inside.2
  simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step_augmented_assignment]
  repeat' split
  all_goals apply Preserves.unchanged layout
  all_goals first
    | rfl
    | trivial
    | (simp [StepWithin, StateWithin, WorkWithin, FrameWithin, envInside] <;> exact ⟨bodyInside, stackInside⟩)
    | simp [relocateStep, relocateState, relocateWork, relocateFrame]

theorem step_empty_block_preserves (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.block [] env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block [] env, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.block [] env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · rfl
  · exact ⟨by trivial, inside.2⟩
  · rfl

theorem step_expression_statement_preserves (expression : Expr) (following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.block (.expr expression :: following) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.expr expression :: following) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.block (.expr expression :: following) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · rfl
  · refine ⟨inside.1.1, ?_⟩
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simp only [FrameWithin]
      exact ⟨inside.1.1, fun statement member => inside.1.2 statement (List.mem_cons_of_mem _ member)⟩
    · exact inside.2 frame member
  · simp only [step, relocateState, relocateWork, List.map_cons, relocateStmt, protectGenerator_next, relocateStep, relocateFrame]

theorem step_if_statement_preserves (condition : Expr) (yes no following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.block (.ifThen condition yes no :: following) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.ifThen condition yes no :: following) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.block (.ifThen condition yes no :: following) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have branches := inside.1.2 _ (List.mem_cons_self ..)
  simp only [StmtWithin] at branches
  apply Preserves.unchanged layout
  · rfl
  · refine ⟨inside.1.1, ?_⟩
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simp only [FrameWithin]
      exact ⟨inside.1.1, branches.1, branches.2,
        fun statement member => inside.1.2 statement (List.mem_cons_of_mem _ member)⟩
    · exact inside.2 frame member
  · simp only [step, relocateState, relocateWork, List.map_cons, relocateStmt, protectGenerator_next, relocateStep, relocateFrame]

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.HeapCalls

/-- An attribute annotation evaluates its receiver, without reading the field or the annotation. -/
theorem BlockContinues.annotationAttribute
    {module : Module} {globals : Mutable.Globals} {env : Env} {base annotation : Expr} {field : String}
    {heap after : Mutable.Heap} {value : Mutable.Value}
    (target : Evaluates (globals := globals) module env base heap value after) :
    BlockContinues (globals := globals) module env [.annAssign (.attribute base field) annotation none] heap env after := by
  intro following anchors stack
  exact .next rfl ((target anchors (.discard following env :: stack)).trans (.next rfl .refl))

end FormalSW.PyAst.HeapCalls
