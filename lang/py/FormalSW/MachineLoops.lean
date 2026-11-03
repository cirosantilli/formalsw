import lang.py.FormalSW.MachineControl
import lang.py.FormalSW.ListInplaceRelocation

/-! Loop boundaries and live sequence cursors retain their meaning across heap layouts. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem loopControlStmt_relocate (rename : Nat → Nat) (statement : Stmt) :
    Calls.loopControlStmt (relocateStmt rename statement) = Calls.loopControlStmt statement := by
  induction statement using Stmt.rec
    (motive_2 := fun body => Calls.loopControl (body.map (relocateStmt rename)) = Calls.loopControl body) <;>
    simp_all [relocateStmt, Calls.loopControlStmt, Calls.loopControl]

theorem loopControl_relocate (rename : Nat → Nat) (body : List Stmt) :
    Calls.loopControl (body.map (relocateStmt rename)) = Calls.loopControl body := by
  induction body with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, Calls.loopControl, loopControlStmt_relocate, ih]

theorem loopContinuation_relocate (rename : Nat → Nat) (body : List Stmt) (next : Stmt) :
    Calls.loopContinuation (body.map (relocateStmt rename)) (relocateStmt rename next) =
      relocateStmt rename (Calls.loopContinuation body next) := by
  simp only [Calls.loopContinuation, loopControl_relocate]
  split <;> simp only [relocateStmt]

theorem loopContinuation_within (limit : Nat) (body : List Stmt) (next : Stmt)
    (inside : StmtWithin limit next) : StmtWithin limit (Calls.loopContinuation body next) := by
  unfold Calls.loopContinuation
  split <;> simpa only [StmtWithin] using inside

theorem loopTarget_relocate (rename : Nat → Nat) (body : List Stmt) :
    Calls.loopTarget (body.map (relocateStmt rename)) =
      (Calls.loopTarget body).map (fun pair => (relocateStmt rename pair.1, pair.2.map (relocateStmt rename))) := by
  induction body with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [relocateStmt, Calls.loopTarget, ih]

theorem loopTarget_within (limit : Nat) (body : List Stmt) (next : Stmt) (following : List Stmt)
    (inside : ∀ statement ∈ body, StmtWithin limit statement)
    (found : Calls.loopTarget body = some (next, following)) :
    StmtWithin limit next ∧ ∀ statement ∈ following, StmtWithin limit statement := by
  induction body with
  | nil => cases found
  | cons head tail ih =>
    have headInside := inside head (by simp)
    have tailInside : ∀ statement ∈ tail, StmtWithin limit statement :=
      fun statement member => inside statement (by simp [member])
    cases head <;> simp only [Calls.loopTarget] at found
    all_goals first
      | exact ih tailInside found
      | cases found; exact ⟨by simpa only [StmtWithin] using headInside, tailInside⟩

variable (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
  (logicalAnchors physicalAnchors : Nat)

theorem step_while_relocates (condition : Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.block (.whileDo condition body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.block (.whileDo condition body otherwise :: following) env, stack, logical⟩ globals) := by
  simp [relocateState, relocateWork, relocateStmt, step, relocateStep, relocateFrame,
    List.map_append, ← loopContinuation_relocate]

theorem step_range_loop_relocates (name : String) (next stop stride : Int) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.block (.rangeStepLoop name next stop stride body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.block (.rangeStepLoop name next stop stride body otherwise :: following) env, stack, logical⟩ globals) := by
  cases test : Calls.rangeContinues next stop stride <;>
    simp [relocateState, relocateWork, relocateStmt, step, test, relocateStep, relocateEnv_set,
      List.map_append, ← loopContinuation_relocate, relocateValue]

theorem step_loopResume_relocates (next : Stmt) (following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.block (.loopResume next :: following) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.block (.loopResume next :: following) env, stack, logical⟩ globals) := by
  simp [relocateState, relocateWork, relocateStmt, step, relocateStep]

theorem step_break_relocates (following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.block (.breakLoop :: following) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.block (.breakLoop :: following) env, stack, logical⟩ globals) := by
  cases target : Calls.loopTarget following with
  | none => simp [relocateState, relocateWork, relocateStmt, step, loopTarget_relocate, target, relocateStep]
  | some pair =>
    rcases pair with ⟨next, rest⟩
    simp [relocateState, relocateWork, relocateStmt, step, loopTarget_relocate, target, relocateStep]

theorem step_continue_relocates (following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.block (.continueLoop :: following) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.block (.continueLoop :: following) env, stack, logical⟩ globals) := by
  cases target : Calls.loopTarget following with
  | none => simp [relocateState, relocateWork, relocateStmt, step, loopTarget_relocate, target, relocateStep]
  | some pair =>
    rcases pair with ⟨next, rest⟩
    simp [relocateState, relocateWork, relocateStmt, step, loopTarget_relocate, target, relocateStep]

theorem sequenceValue_relocate (source : SequenceSource) :
    sequenceValue (relocateSource rename source) = relocateValue rename (sequenceValue source) := by
  cases source <;> rfl

theorem SourceWithin.value {limit : Nat} {source : SequenceSource} (inside : SourceWithin limit source) :
    (sequenceValue source).edge.Within limit := by
  cases source <;> exact inside

/-- Read the current sequence at each step, including after mutations and past its new end. -/
theorem step_sequence_loop_relocates (layout : RuntimeLayout logical physical rename)
    (name : String) (source : SequenceSource) (position : Nat) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : SourceWithin logical.length source) :
    step module physicalAnchors
        (relocateState rename physical ⟨.block (.sequenceStepLoop name source position body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.block (.sequenceStepLoop name source position body otherwise :: following) env, stack, logical⟩ globals) := by
  have paired := layout.sequence (sequenceValue source) inside.value
  cases read : Mutable.sequence (sequenceValue source) logical with
  | none =>
    simp [relocateState, relocateWork, relocateStmt, step, run, sequenceValue_relocate,
      paired, read, relocateStep]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have unchanged := sequence_keeps_heap logical after (sequenceValue source) outcome read
    subst after
    cases outcome with
    | error exception =>
      simp [relocateState, relocateWork, relocateStmt, step, run, sequenceValue_relocate,
        paired, read, Except.map, done, relocateStep, relocateCompletion, protectGenerator, Function.comp_def, relocateFrame_inGenerator]
    | ok items =>
      cases item : items[position]? <;>
        simp [relocateState, relocateWork, relocateStmt, step, run, sequenceValue_relocate,
          paired, read, Except.map, List.getElem?_map, item, relocateStep, relocateEnv_set,
          ← loopContinuation_relocate]

variable (heap : Mutable.Heap) (anchors : Nat)

theorem StateWithin.while_loop (condition : Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin ⟨.block (.whileDo condition body otherwise :: following) env, stack, heap⟩) :
    StepWithin (step module anchors ⟨.block (.whileDo condition body otherwise :: following) env, stack, heap⟩ globals) := by
  have loopInside := inside.1.2 (.whileDo condition body otherwise) (by simp)
  have restInside : ∀ statement ∈ following, StmtWithin heap.length statement :=
    fun statement member => inside.1.2 statement (by simp [member])
  have nextInside := loopContinuation_within heap.length body (.whileDo condition body otherwise) loopInside
  simp only [StmtWithin] at loopInside
  simp only [step, protectGenerator_next, StepWithin, StateWithin, WorkWithin]
  refine ⟨inside.1.1, ?_⟩
  intro frame member
  rcases List.mem_cons.mp member with rfl | member
  · simp only [FrameWithin]
    exact ⟨inside.1.1, by simpa only [List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq] using And.intro loopInside.1 nextInside, loopInside.2, restInside⟩
  · exact inside.2 frame member

theorem StateWithin.range_loop (name : String) (next stop stride : Int) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin ⟨.block (.rangeStepLoop name next stop stride body otherwise :: following) env, stack, heap⟩) :
    StepWithin (step module anchors ⟨.block (.rangeStepLoop name next stop stride body otherwise :: following) env, stack, heap⟩ globals) := by
  have loopInside := inside.1.2 (.rangeStepLoop name next stop stride body otherwise) (by simp)
  have restInside : ∀ statement ∈ following, StmtWithin heap.length statement :=
    fun statement member => inside.1.2 statement (by simp [member])
  have nextInside := loopContinuation_within heap.length body
    (.rangeStepLoop name (next + stride) stop stride body otherwise) (by simpa only [StmtWithin] using loopInside)
  simp only [StmtWithin] at loopInside
  cases test : Calls.rangeContinues next stop stride <;>
    simp only [step, test, Bool.false_eq_true, if_false, if_true, protectGenerator_next, StepWithin, StateWithin, WorkWithin]
  · exact ⟨⟨inside.1.1, by simpa only [List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq] using And.intro loopInside.2 restInside⟩, inside.2⟩
  · exact ⟨⟨inside.1.1.setLocal name (.scalar (.int next)) (by trivial),
      by simpa only [List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq] using And.intro (And.intro loopInside.1 nextInside) restInside⟩, inside.2⟩

theorem StateWithin.loopResume (next : Stmt) (following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin ⟨.block (.loopResume next :: following) env, stack, heap⟩) :
    StepWithin (step module anchors ⟨.block (.loopResume next :: following) env, stack, heap⟩ globals) := by
  have nextInside := inside.1.2 (.loopResume next) (by simp)
  refine ⟨⟨inside.1.1, ?_⟩, inside.2⟩
  intro statement member
  rcases List.mem_cons.mp member with rfl | member
  · simpa only [StmtWithin] using nextInside
  · exact inside.1.2 statement (by simp [member])

theorem StateWithin.break_loop (following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin ⟨.block (.breakLoop :: following) env, stack, heap⟩) :
    StepWithin (step module anchors ⟨.block (.breakLoop :: following) env, stack, heap⟩ globals) := by
  cases target : Calls.loopTarget following with
  | none => simp [step, target, StepWithin, protectGenerator]
  | some pair =>
    rcases pair with ⟨next, rest⟩
    have bounded := loopTarget_within heap.length following next rest
      (fun statement member => inside.1.2 statement (by simp [member])) target
    simp only [step, target, protectGenerator_next, StepWithin]
    exact ⟨⟨inside.1.1, bounded.2⟩, inside.2⟩

theorem StateWithin.continue_loop (following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin ⟨.block (.continueLoop :: following) env, stack, heap⟩) :
    StepWithin (step module anchors ⟨.block (.continueLoop :: following) env, stack, heap⟩ globals) := by
  cases target : Calls.loopTarget following with
  | none => simp [step, target, StepWithin, protectGenerator]
  | some pair =>
    rcases pair with ⟨next, rest⟩
    have bounded := loopTarget_within heap.length following next rest
      (fun statement member => inside.1.2 statement (by simp [member])) target
    simp only [step, target, protectGenerator_next, StepWithin]
    exact ⟨⟨inside.1.1, by simpa using bounded⟩, inside.2⟩

theorem StateWithin.sequence_loop (closed : Closed heap)
    (name : String) (source : SequenceSource) (position : Nat) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (globalsInside : GlobalsWithin heap.length globals)
    (inside : StateWithin ⟨.block (.sequenceStepLoop name source position body otherwise :: following) env, stack, heap⟩) :
    StepWithin (step module anchors ⟨.block (.sequenceStepLoop name source position body otherwise :: following) env, stack, heap⟩ globals) := by
  have loopInside := inside.1.2 (.sequenceStepLoop name source position body otherwise) (by simp)
  have restInside : ∀ statement ∈ following, StmtWithin heap.length statement :=
    fun statement member => inside.1.2 statement (by simp [member])
  have nextInside := loopContinuation_within heap.length body
    (.sequenceStepLoop name source (position + 1) body otherwise) (by simpa only [StmtWithin] using loopInside)
  simp only [StmtWithin] at loopInside
  cases read : Mutable.sequence (sequenceValue source) heap with
  | none => simp [step, run, read, StepWithin, protectGenerator]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have unchanged := sequence_keeps_heap heap after (sequenceValue source) outcome read
    subst after
    cases outcome with
    | error exception =>
      simp only [step, run, read, done]
      apply protectGenerator_within
      exact ⟨globalsInside, by intro value impossible; cases impossible⟩
    | ok items =>
      have itemsInside := sequence_items_within heap heap closed (sequenceValue source) items read
      cases item : items[position]? with
      | none =>
        simp only [step, run, read, item, protectGenerator_next, StepWithin]
        exact ⟨⟨inside.1.1, by
          simpa only [List.mem_append, or_imp, forall_and] using And.intro loopInside.2.2 restInside⟩, inside.2⟩
      | some value =>
        simp only [step, run, read, item, protectGenerator_next, StepWithin]
        exact ⟨⟨inside.1.1.setLocal name value (itemsInside value (List.mem_of_getElem? item)), by
          simpa only [List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq]
            using And.intro (And.intro loopInside.2.1 nextInside) restInside⟩, inside.2⟩

end FormalSW.PyAst.HeapCalls.Relocation
