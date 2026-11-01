import lang.py.FormalSW.MachineExpressions

/-! Truth-dependent steps preserve short-circuiting and retained object identities. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem step_boolean_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
    (value : Value) (op : BoolOp) (rest : List Expr) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : value.edge.Within logical.length) :
    step module physicalAnchors
        (relocateState rename physical ⟨.value value, .boolean op rest env :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value value, .boolean op rest env :: stack, logical⟩ globals) := by
  obtain ⟨truth, tested⟩ := truth_total logical value inside
  have paired := layout.truth value inside
  cases op <;> cases truth <;> cases rest <;>
    simp [relocateState, relocateWork, List.map_cons, relocateFrame, step, run, tested, paired, relocateStep]

theorem StateWithin.boolean (module : Module) (heap : Mutable.Heap) (anchors : Nat)
    (value : Value) (op : BoolOp) (rest : List Expr) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin ⟨.value value, .boolean op rest env :: stack, heap⟩) :
    StepWithin (step module anchors ⟨.value value, .boolean op rest env :: stack, heap⟩ globals) := by
  have envInside := inside.2 (.boolean op rest env) (by simp)
  simp only [FrameWithin] at envInside
  have stackInside : ∀ frame ∈ stack, FrameWithin heap.length frame :=
    fun frame member => inside.2 frame (by simp [member])
  obtain ⟨truth, tested⟩ := truth_total heap value inside.1
  cases op <;> cases truth <;> cases rest <;>
    simp only [step, run, tested, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      if_true, if_false, protectGenerator_next, StepWithin, StateWithin, WorkWithin] <;>
    first
    | exact ⟨inside.1, stackInside⟩
    | exact ⟨envInside, fun frame member => by
        rcases List.mem_cons.mp member with rfl | member
        · simpa only [FrameWithin] using envInside
        · exact stackInside frame member⟩

theorem step_conditional_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
    (value : Value) (yes no : Expr) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : value.edge.Within logical.length) :
    step module physicalAnchors
        (relocateState rename physical ⟨.value value, .conditional yes no env :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value value, .conditional yes no env :: stack, logical⟩ globals) := by
  obtain ⟨truth, tested⟩ := truth_total logical value inside
  have paired := layout.truth value inside
  simp [relocateState, relocateWork, List.map_cons, relocateFrame, step, run, tested, paired, relocateStep]

theorem StateWithin.conditional (module : Module) (heap : Mutable.Heap) (anchors : Nat)
    (value : Value) (yes no : Expr) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin ⟨.value value, .conditional yes no env :: stack, heap⟩) :
    StepWithin (step module anchors ⟨.value value, .conditional yes no env :: stack, heap⟩ globals) := by
  have envInside := inside.2 (.conditional yes no env) (by simp)
  simp only [FrameWithin] at envInside
  obtain ⟨truth, tested⟩ := truth_total heap value inside.1
  simp only [step, run, tested, protectGenerator_next, StepWithin]
  exact ⟨envInside, fun frame member => inside.2 frame (by simp [member])⟩

theorem step_branch_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
    (value : Value) (yes no following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : value.edge.Within logical.length) :
    step module physicalAnchors
        (relocateState rename physical ⟨.value value, .branch yes no following env :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value value, .branch yes no following env :: stack, logical⟩ globals) := by
  obtain ⟨truth, tested⟩ := truth_total logical value inside
  have paired := layout.truth value inside
  cases truth <;>
    simp [relocateState, relocateWork, List.map_cons, relocateFrame, step, run, tested, paired, relocateStep]

theorem StateWithin.branch (module : Module) (heap : Mutable.Heap) (anchors : Nat)
    (value : Value) (yes no following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin ⟨.value value, .branch yes no following env :: stack, heap⟩) :
    StepWithin (step module anchors ⟨.value value, .branch yes no following env :: stack, heap⟩ globals) := by
  have saved := inside.2 (.branch yes no following env) (by simp)
  simp only [FrameWithin] at saved
  have stackInside : ∀ frame ∈ stack, FrameWithin heap.length frame :=
    fun frame member => inside.2 frame (by simp [member])
  obtain ⟨truth, tested⟩ := truth_total heap value inside.1
  cases truth <;> simp only [step, run, tested, Bool.false_eq_true, if_false, if_true,
    protectGenerator_next, StepWithin, StateWithin, WorkWithin]
  · exact ⟨⟨saved.1, fun statement member => (List.mem_append.mp member).elim (saved.2.2.1 statement) (saved.2.2.2 statement)⟩, stackInside⟩
  · exact ⟨⟨saved.1, fun statement member => (List.mem_append.mp member).elim (saved.2.1 statement) (saved.2.2.2 statement)⟩, stackInside⟩

theorem step_chainResult_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
    (value right : Value) (rest : List (CmpOp × Expr)) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : value.edge.Within logical.length) :
    step module physicalAnchors
        (relocateState rename physical ⟨.value value, .chainResult right rest env :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value value, .chainResult right rest env :: stack, logical⟩ globals) := by
  obtain ⟨truth, tested⟩ := truth_total logical value inside
  have paired := layout.truth value inside
  cases rest with
  | nil => simp [relocateState, relocateWork, List.map_cons, relocateFrame, step, relocateStep]
  | cons next rest =>
    rcases next with ⟨op, expression⟩
    cases truth <;>
      simp [relocateState, relocateWork, List.map_cons, relocateFrame, step, run, tested, paired, relocateStep]

theorem StateWithin.chainResult (module : Module) (heap : Mutable.Heap) (anchors : Nat)
    (value right : Value) (rest : List (CmpOp × Expr)) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin ⟨.value value, .chainResult right rest env :: stack, heap⟩) :
    StepWithin (step module anchors ⟨.value value, .chainResult right rest env :: stack, heap⟩ globals) := by
  have saved := inside.2 (.chainResult right rest env) (by simp)
  simp only [FrameWithin] at saved
  have stackInside : ∀ frame ∈ stack, FrameWithin heap.length frame :=
    fun frame member => inside.2 frame (by simp [member])
  obtain ⟨truth, tested⟩ := truth_total heap value inside.1
  cases rest with
  | nil => exact ⟨inside.1, stackInside⟩
  | cons next rest =>
    rcases next with ⟨op, expression⟩
    cases truth <;> simp only [step, run, tested, Bool.false_eq_true, if_false, if_true,
      protectGenerator_next, StepWithin, StateWithin, WorkWithin]
    · exact ⟨inside.1, stackInside⟩
    · refine ⟨saved.2, ?_⟩
      intro frame member
      rcases List.mem_cons.mp member with rfl | member
      · simpa only [FrameWithin] using saved
      · exact stackInside frame member

end FormalSW.PyAst.HeapCalls.Relocation
