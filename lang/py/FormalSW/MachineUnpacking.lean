import lang.py.FormalSW.MachineLoopEntry

/-! Sequence unpacking preserves shared fields, validation order, and repeated target names. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem assignNames_relocate (rename : Nat → Nat) (env : Env) (names : List String) (values : List Value) :
    assignNames (relocateEnv rename env) names (values.map (relocateValue rename)) =
      relocateEnv rename (assignNames env names values) := by
  induction names generalizing env values with
  | nil => rfl
  | cons name names ih =>
    cases values with
    | nil => rfl
    | cons value values =>
      change assignNames (setLocal (relocateEnv rename env) name (relocateValue rename value)) names
          (values.map (relocateValue rename)) =
        relocateEnv rename (assignNames (setLocal env name value) names values)
      rw [← relocateEnv_set, ih]

theorem EnvWithin.assignNames {limit : Nat} {env : Env} (inside : EnvWithin limit env)
    (names : List String) (values : List Value) (valuesInside : ∀ value ∈ values, value.edge.Within limit) :
    EnvWithin limit (assignNames env names values) := by
  induction names generalizing env values with
  | nil => exact inside
  | cons name names ih =>
    cases values with
    | nil => exact inside
    | cons value values =>
      exact ih (inside.setLocal name value (valuesInside value (by simp))) values
        (fun item member => valuesInside item (by simp [member]))

/-- Sequence extraction is read-only, including exceptional and unsupported results. -/
theorem run_sequence_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
    (value : Value) (inside : value.edge.Within logical.length) (globals : Mutable.Globals)
    (next otherNext : List Value → Mutable.Heap → Step State Mutable.Completion)
    (pairedNext : ∀ items, Mutable.sequence value logical = some (.ok items, logical) →
      otherNext (items.map (relocateValue rename)) physical =
        relocateStep rename physical physicalAnchors (next items logical)) :
    run (globals := relocateGlobals rename globals) physicalAnchors physical
        (Mutable.sequence (relocateValue rename value)) otherNext =
      relocateStep rename physical physicalAnchors
        (run (globals := globals) logicalAnchors logical (Mutable.sequence value) next) := by
  have paired := layout.sequence value inside
  cases read : Mutable.sequence value logical with
  | none => simp [run, paired, read, relocateStep]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have unchanged := sequence_keeps_heap logical after value outcome read
    subst after
    cases outcome with
    | error exception => simp [run, paired, read, Except.map, done, relocateStep, relocateCompletion]
    | ok items => simpa only [run, paired, read, Option.map_some, Except.map] using pairedNext items read

theorem run_sequence_within (heap : Mutable.Heap) (anchors : Nat) (value : Value) (globals : Mutable.Globals)
    (globalsInside : GlobalsWithin heap.length globals)
    (next : List Value → Mutable.Heap → Step State Mutable.Completion)
    (nextInside : ∀ items, Mutable.sequence value heap = some (.ok items, heap) → StepWithin (next items heap)) :
    StepWithin (run (globals := globals) anchors heap (Mutable.sequence value) next) := by
  cases read : Mutable.sequence value heap with
  | none => simp [run, read, StepWithin]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have unchanged := sequence_keeps_heap heap after value outcome read
    subst after
    cases outcome with
    | error exception =>
      simp only [run, read, done]
      exact ⟨globalsInside, by intro result impossible; cases impossible⟩
    | ok items => simpa only [run, read] using nextInside items read

variable (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
  (logicalAnchors physicalAnchors : Nat)

theorem step_unpack_relocates (layout : RuntimeLayout logical physical rename)
    (value : Value) (names : List String) (following : List Stmt) (env : Env) (stack : List Frame)
    (globals : Mutable.Globals) (inside : value.edge.Within logical.length) :
    step module physicalAnchors
        (relocateState rename physical ⟨.value value, .unpack names following env :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value value, .unpack names following env :: stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateFrame, step]
  rw [← protectGenerator_relocates]
  simp only [List.map_cons, relocateFrame]
  congr 1
  apply run_sequence_relocates logical physical rename layout logicalAnchors physicalAnchors value inside globals
  intro items read
  by_cases arity : names.length = items.length <;>
    simp [arity, relocateStep, relocateState, relocateWork, assignNames_relocate, done, relocateCompletion, Except.map]

theorem step_unpack_start_relocates (layout : RuntimeLayout logical physical rename)
    (value : Value) (names : List String) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (inside : value.edge.Within logical.length) :
    step module physicalAnchors
        (relocateState rename physical ⟨.value value, .unpackSequence names body otherwise following env :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value value, .unpackSequence names body otherwise following env :: stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateFrame, step]
  rw [← protectGenerator_relocates]
  simp only [List.map_cons, relocateFrame]
  congr 1
  apply run_sequence_relocates logical physical rename layout logicalAnchors physicalAnchors value inside globals
  intro items read
  simp only [relocateStep, relocateState, relocateWork, List.map_cons, relocateStmt, sequenceSource_relocate]

theorem step_unpack_loop_relocates (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (names : List String) (source : SequenceSource) (position : Nat) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (inside : SourceWithin logical.length source) :
    step module physicalAnchors
        (relocateState rename physical ⟨.block (.unpackStepLoop names source position body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.block (.unpackStepLoop names source position body otherwise :: following) env, stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step, sequenceValue_relocate]
  rw [← protectGenerator_relocates]
  congr 1
  apply run_sequence_relocates logical physical rename layout logicalAnchors physicalAnchors (sequenceValue source) inside.value globals
  intro items read
  cases item : items[position]? with
  | none => simp [List.getElem?_map, item, relocateStep, relocateState, relocateWork]
  | some value =>
    simp only [List.getElem?_map, item, Option.map_some]
    apply run_sequence_relocates logical physical rename layout logicalAnchors physicalAnchors value
      (sequence_items_within logical logical closed (sequenceValue source) items read value (List.mem_of_getElem? item)) globals
    intro fields unpacked
    by_cases arity : names.length = fields.length <;>
      simp [arity, relocateStep, relocateState, relocateWork, assignNames_relocate, done, relocateCompletion,
        Except.map, ← loopContinuation_relocate, relocateStmt]

variable (heap : Mutable.Heap) (anchors : Nat)

theorem StateWithin.unpack (closed : Closed heap) (value : Value) (names : List String) (following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (globalsInside : GlobalsWithin heap.length globals)
    (inside : StateWithin ⟨.value value, .unpack names following env :: stack, heap⟩) :
    StepWithin (step module anchors ⟨.value value, .unpack names following env :: stack, heap⟩ globals) := by
  have saved := inside.2 (.unpack names following env) (by simp)
  simp only [FrameWithin] at saved
  simp only [step]
  apply protectGenerator_within
  apply run_sequence_within heap anchors value globals globalsInside
  intro items read
  split
  · exact ⟨⟨saved.1.assignNames names items (sequence_items_within heap heap closed value items read), saved.2⟩,
      fun frame member => inside.2 frame (by simp [member])⟩
  · exact ⟨globalsInside, by intro result impossible; cases impossible⟩

theorem StateWithin.unpack_start (value : Value) (names : List String) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (globalsInside : GlobalsWithin heap.length globals)
    (inside : StateWithin ⟨.value value, .unpackSequence names body otherwise following env :: stack, heap⟩) :
    StepWithin (step module anchors ⟨.value value, .unpackSequence names body otherwise following env :: stack, heap⟩ globals) := by
  have saved := inside.2 (.unpackSequence names body otherwise following env) (by simp)
  simp only [FrameWithin] at saved
  simp only [step]
  apply protectGenerator_within
  apply run_sequence_within heap anchors value globals globalsInside
  intro items read
  refine ⟨⟨saved.1, ?_⟩, fun frame member => inside.2 frame (by simp [member])⟩
  intro statement member
  rcases List.mem_cons.mp member with rfl | member
  · simp only [StmtWithin]
    exact ⟨sequenceSource_within heap.length value inside.1, saved.2.1, saved.2.2.1⟩
  · exact saved.2.2.2 statement member

theorem StateWithin.unpack_loop (closed : Closed heap)
    (names : List String) (source : SequenceSource) (position : Nat) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (globalsInside : GlobalsWithin heap.length globals)
    (inside : StateWithin ⟨.block (.unpackStepLoop names source position body otherwise :: following) env, stack, heap⟩) :
    StepWithin (step module anchors ⟨.block (.unpackStepLoop names source position body otherwise :: following) env, stack, heap⟩ globals) := by
  have loopInside := inside.1.2 (.unpackStepLoop names source position body otherwise) (by simp)
  have restInside : ∀ statement ∈ following, StmtWithin heap.length statement :=
    fun statement member => inside.1.2 statement (by simp [member])
  have nextInside := loopContinuation_within heap.length body
    (.unpackStepLoop names source (position + 1) body otherwise) (by simpa only [StmtWithin] using loopInside)
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
    apply run_sequence_within heap anchors value globals globalsInside
    intro fields unpacked
    split
    · exact ⟨⟨inside.1.1.assignNames names fields (sequence_items_within heap heap closed value fields unpacked), by
        simpa only [List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq]
          using And.intro (And.intro loopInside.2.1 nextInside) restInside⟩, inside.2⟩
    · exact ⟨globalsInside, by intro result impossible; cases impossible⟩

end FormalSW.PyAst.HeapCalls.Relocation
