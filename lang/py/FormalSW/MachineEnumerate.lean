import lang.py.FormalSW.MachineUnpacking

/-! Enumerate retains the source while evaluating its start and binds each item after its index. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem enumerateStart_total (heap : Mutable.Heap) (value : Value) :
    ∃ outcome, enumerateStart value heap = some (outcome, heap) := by
  cases value with
  | scalar scalar => cases scalar <;> exact ⟨_, rfl⟩
  | ref address => exact ⟨_, rfl⟩

theorem enumerateStart_relocate (logical physical : Mutable.Heap) (rename : Nat → Nat) (value : Value) :
    enumerateStart (relocateValue rename value) physical =
      (enumerateStart value logical).map (fun pair => (pair.1, physical)) := by
  cases value with
  | scalar scalar => cases scalar <;> rfl
  | ref address => rfl

variable (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
  (logicalAnchors physicalAnchors : Nat)

theorem step_for_enumerate (asList : Bool) (index name : String) (iterable : Expr) (start : Option Expr)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module logicalAnchors
        ⟨.block (.forIn (if asList then .list [.name index, .name name] else .tuple [.name index, .name name])
          (.call (.name "enumerate") (iterable :: start.toList)) body otherwise :: following) env, stack, logical⟩ globals =
      .next ⟨.expr iterable env,
        .enumerateSource index name (start.getD (.constant (.int 0))) body otherwise following env :: stack, logical⟩ := by
  cases asList <;> cases start <;> rfl

theorem step_for_enumerate_relocates (asList : Bool) (index name : String) (iterable : Expr) (start : Option Expr)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical
          ⟨.block (.forIn (if asList then .list [.name index, .name name] else .tuple [.name index, .name name])
            (.call (.name "enumerate") (iterable :: start.toList)) body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors
          ⟨.block (.forIn (if asList then .list [.name index, .name name] else .tuple [.name index, .name name])
            (.call (.name "enumerate") (iterable :: start.toList)) body otherwise :: following) env, stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step_for_enumerate,
    relocateStep, relocateFrame]

theorem step_enumerate_source_relocates (index name : String) (value : Value) (start : Expr)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.value value, .enumerateSource index name start body otherwise following env :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value value, .enumerateSource index name start body otherwise following env :: stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateFrame, step, protectGenerator_next, relocateStep]

theorem step_enumerate_start_relocates (layout : RuntimeLayout logical physical rename)
    (index name : String) (source value : Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (sourceInside : source.edge.Within logical.length) :
    step module physicalAnchors
        (relocateState rename physical ⟨.value value, .enumerateStart index name source body otherwise following env :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value value, .enumerateStart index name source body otherwise following env :: stack, logical⟩ globals) := by
  obtain ⟨outcome, tested⟩ := enumerateStart_total logical value
  have paired : enumerateStart (relocateValue rename value) physical = some (outcome, physical) := by
    rw [enumerateStart_relocate logical physical rename value, tested]
    rfl
  simp only [relocateState, relocateWork, List.map_cons, relocateFrame, step]
  rw [← protectGenerator_relocates]
  simp only [List.map_cons, relocateFrame]
  congr 1
  cases outcome with
  | error exception => simp [run, tested, paired, done, relocateStep, relocateCompletion, Except.map]
  | ok counter =>
    simp only [run, tested, paired]
    apply run_sequence_relocates logical physical rename layout logicalAnchors physicalAnchors source sourceInside globals
    intro items read
    simp only [relocateStep, relocateState, relocateWork, List.map_cons, relocateStmt, sequenceSource_relocate]

theorem step_enumerate_loop_relocates (layout : RuntimeLayout logical physical rename)
    (index name : String) (source : SequenceSource) (position : Nat) (counter : Int) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (inside : SourceWithin logical.length source) :
    step module physicalAnchors
        (relocateState rename physical
          ⟨.block (.enumerateStepLoop index name source position counter body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors
          ⟨.block (.enumerateStepLoop index name source position counter body otherwise :: following) env, stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step, sequenceValue_relocate]
  rw [← protectGenerator_relocates]
  congr 1
  apply run_sequence_relocates logical physical rename layout logicalAnchors physicalAnchors (sequenceValue source) inside.value globals
  intro items read
  cases item : items[position]? <;>
    simp [List.getElem?_map, item, relocateStep, relocateState, relocateWork,
      relocateEnv_set, relocateValue, ← loopContinuation_relocate, relocateStmt]

variable (heap : Mutable.Heap) (anchors : Nat)

theorem StateWithin.for_enumerate (asList : Bool) (index name : String) (iterable : Expr) (start : Option Expr)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin
      ⟨.block (.forIn (if asList then .list [.name index, .name name] else .tuple [.name index, .name name])
        (.call (.name "enumerate") (iterable :: start.toList)) body otherwise :: following) env, stack, heap⟩) :
    StepWithin (step module anchors
      ⟨.block (.forIn (if asList then .list [.name index, .name name] else .tuple [.name index, .name name])
        (.call (.name "enumerate") (iterable :: start.toList)) body otherwise :: following) env, stack, heap⟩ globals) := by
  have loopInside := inside.1.2 _ (List.mem_cons_self ..)
  simp only [StmtWithin] at loopInside
  rw [step_for_enumerate]
  refine ⟨inside.1.1, ?_⟩
  intro frame member
  rcases List.mem_cons.mp member with rfl | member
  · simp only [FrameWithin]
    exact ⟨inside.1.1, loopInside.1, loopInside.2, fun statement member => inside.1.2 statement (by simp [member])⟩
  · exact inside.2 frame member

theorem StateWithin.enumerate_source (index name : String) (value : Value) (start : Expr)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin ⟨.value value, .enumerateSource index name start body otherwise following env :: stack, heap⟩) :
    StepWithin (step module anchors ⟨.value value, .enumerateSource index name start body otherwise following env :: stack, heap⟩ globals) := by
  have saved := inside.2 (.enumerateSource index name start body otherwise following env) (by simp)
  simp only [FrameWithin] at saved
  refine ⟨saved.1, ?_⟩
  intro frame member
  rcases List.mem_cons.mp member with rfl | member
  · simp only [FrameWithin]
    exact ⟨inside.1, saved⟩
  · exact inside.2 frame (by simp [member])

theorem StateWithin.enumerate_start (index name : String) (source value : Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (globalsInside : GlobalsWithin heap.length globals)
    (inside : StateWithin ⟨.value value, .enumerateStart index name source body otherwise following env :: stack, heap⟩) :
    StepWithin (step module anchors ⟨.value value, .enumerateStart index name source body otherwise following env :: stack, heap⟩ globals) := by
  have saved := inside.2 (.enumerateStart index name source body otherwise following env) (by simp)
  simp only [FrameWithin] at saved
  obtain ⟨outcome, tested⟩ := enumerateStart_total heap value
  simp only [step]
  apply protectGenerator_within
  cases outcome with
  | error exception =>
    simp only [run, tested, done]
    exact ⟨globalsInside, by intro result impossible; cases impossible⟩
  | ok counter =>
    simp only [run, tested]
    apply run_sequence_within heap anchors source globals globalsInside
    intro items read
    refine ⟨⟨saved.2.1, ?_⟩, fun frame member => inside.2 frame (by simp [member])⟩
    intro statement member
    rcases List.mem_cons.mp member with rfl | member
    · simp only [StmtWithin]
      exact ⟨sequenceSource_within heap.length source saved.1, saved.2.2.1, saved.2.2.2.1⟩
    · exact saved.2.2.2.2 statement member

theorem StateWithin.enumerate_loop (closed : Closed heap)
    (index name : String) (source : SequenceSource) (position : Nat) (counter : Int) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (globalsInside : GlobalsWithin heap.length globals)
    (inside : StateWithin
      ⟨.block (.enumerateStepLoop index name source position counter body otherwise :: following) env, stack, heap⟩) :
    StepWithin (step module anchors
      ⟨.block (.enumerateStepLoop index name source position counter body otherwise :: following) env, stack, heap⟩ globals) := by
  have loopInside := inside.1.2 _ (List.mem_cons_self ..)
  have restInside : ∀ statement ∈ following, StmtWithin heap.length statement :=
    fun statement member => inside.1.2 statement (by simp [member])
  have nextInside := loopContinuation_within heap.length body
    (.enumerateStepLoop index name source (position + 1) (counter + 1) body otherwise)
    (by simpa only [StmtWithin] using loopInside)
  simp only [StmtWithin] at loopInside
  simp only [step]
  apply protectGenerator_within
  apply run_sequence_within heap anchors (sequenceValue source) globals globalsInside
  intro items read
  cases item : items[position]? with
  | none =>
    exact ⟨⟨inside.1.1, by
      simpa only [List.mem_append, or_imp, forall_and] using And.intro loopInside.2.2 restInside⟩, inside.2⟩
  | some value =>
    exact ⟨⟨(inside.1.1.setLocal index (.scalar (.int counter)) (by trivial)).setLocal name value
      (sequence_items_within heap heap closed (sequenceValue source) items read value (List.mem_of_getElem? item)), by
      simpa only [List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq]
        using And.intro (And.intro loopInside.2.1 nextInside) restInside⟩, inside.2⟩

end FormalSW.PyAst.HeapCalls.Relocation
