import lang.py.FormalSW.MachineUnpacking
import lang.py.FormalSW.ReverseCalls

/-! Reverse cursors retain their initial position while reading the current sequence. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

theorem RuntimeLayout.reversibleSequence {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (value : Value) (inside : value.edge.Within logical.length) :
    Mutable.reversibleSequence (relocateValue rename value) physical =
      (Mutable.reversibleSequence value logical).map
        (fun pair => (pair.1.map (List.map (relocateValue rename)), physical)) := by
  cases value with
  | scalar scalar => exact layout.sequence (.scalar scalar) inside
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    cases object : logical[address] with
    | list items | tuple items | bytearray items =>
      simpa [Mutable.reversibleSequence, relocateValue, found, object, moved, relocateObject] using
        layout.sequence (.ref address) inside
    | _ => simp [Mutable.reversibleSequence, relocateValue, found, object, moved, relocateObject, error, unsupported, Except.map]

theorem reversibleSequence_keeps_heap (heap after : Heap) (value : Value) (outcome : Except ExceptionObject (List Value))
    (executed : Mutable.reversibleSequence value heap = some (outcome, after)) : after = heap := by
  cases value with
  | scalar scalar => exact sequence_keeps_heap heap after (.scalar scalar) outcome executed
  | ref address =>
    cases found : heap[address]? with
    | none => simp [Mutable.reversibleSequence, found, unsupported] at executed
    | some object =>
      cases object with
      | list items | tuple items | bytearray items =>
        exact sequence_keeps_heap heap after (.ref address) outcome (by
          simpa [Mutable.reversibleSequence, found] using executed)
      | _ => simp [Mutable.reversibleSequence, found, error, unsupported] at executed <;> exact executed.2.symm

theorem reversibleSequence_sequence (heap after : Heap) (value : Value) (items : List Value)
    (executed : Mutable.reversibleSequence value heap = some (.ok items, after)) :
    Mutable.sequence value heap = some (.ok items, after) := by
  cases value with
  | scalar scalar => exact executed
  | ref address =>
    cases found : heap[address]? with
    | none => simp [Mutable.reversibleSequence, found, unsupported] at executed
    | some object =>
      cases object with
      | list values | tuple values | bytearray values => simpa [Mutable.reversibleSequence, found] using executed
      | _ => simp [Mutable.reversibleSequence, found, error, unsupported] at executed

end FormalSW.PyAst.Mutable.Relocation

namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

/-- Read-only primitive correspondence includes unsupported results and exact exceptions. -/
theorem run_readonly_relocates {α β : Type} (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (action : Mutable.Eval α) (otherAction : Mutable.Eval β)
    (mapValue : α → β) (globals : Mutable.Globals)
    (readonly : ∀ outcome after, action logical = some (outcome, after) → after = logical)
    (paired : otherAction physical = (action logical).map (fun pair => (pair.1.map mapValue, physical)))
    (next : α → Mutable.Heap → Step State Mutable.Completion) (otherNext : β → Mutable.Heap → Step State Mutable.Completion)
    (pairedNext : ∀ value, action logical = some (.ok value, logical) →
      otherNext (mapValue value) physical = relocateStep rename physical physicalAnchors (next value logical)) :
    run (globals := relocateGlobals rename globals) physicalAnchors physical otherAction otherNext =
      relocateStep rename physical physicalAnchors (run (globals := globals) logicalAnchors logical action next) := by
  cases read : action logical with
  | none => simp [run, paired, read, relocateStep]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have unchanged := readonly outcome after read
    subst after
    cases outcome with
    | error exception => simp [run, paired, read, Except.map, done, relocateStep, relocateCompletion]
    | ok value => simpa only [run, paired, read, Option.map_some, Except.map] using pairedNext value read

theorem run_readonly_within {α : Type} (heap : Mutable.Heap) (anchors : Nat) (action : Mutable.Eval α)
    (globals : Mutable.Globals) (globalsInside : GlobalsWithin heap.length globals)
    (readonly : ∀ outcome after, action heap = some (outcome, after) → after = heap)
    (next : α → Mutable.Heap → Step State Mutable.Completion)
    (nextInside : ∀ value, action heap = some (.ok value, heap) → StepWithin (next value heap)) :
    StepWithin (run (globals := globals) anchors heap action next) := by
  cases read : action heap with
  | none => simp [run, read, StepWithin]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have unchanged := readonly outcome after read
    subst after
    cases outcome with
    | error exception =>
      simp only [run, read, done]
      exact ⟨globalsInside, by intro value impossible; cases impossible⟩
    | ok value => simpa only [run, read] using nextInside value read

variable (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
  (logicalAnchors physicalAnchors : Nat)

theorem step_for_reversed_relocates (name : String) (iterable : Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.block (.forReversed name iterable body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.block (.forReversed name iterable body otherwise :: following) env, stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step, protectGenerator_next, relocateStep, relocateFrame]

theorem step_reverse_start_relocates (layout : RuntimeLayout logical physical rename)
    (name : String) (value : Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (inside : value.edge.Within logical.length) :
    step module physicalAnchors
        (relocateState rename physical ⟨.value value, .reverseSequence name body otherwise following env :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value value, .reverseSequence name body otherwise following env :: stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateFrame, step]
  rw [← protectGenerator_relocates]
  simp only [List.map_cons, relocateFrame]
  congr 1
  apply run_readonly_relocates logical physical rename logicalAnchors physicalAnchors
    (Mutable.reversibleSequence value) (Mutable.reversibleSequence (relocateValue rename value))
    (List.map (relocateValue rename)) globals
    (fun outcome after executed => reversibleSequence_keeps_heap logical after value outcome executed)
    (layout.reversibleSequence value inside)
  intro items read
  simp only [relocateStep, relocateState, relocateWork, List.map_cons, relocateStmt, List.length_map, sequenceSource_relocate]

theorem step_reverse_loop_relocates (layout : RuntimeLayout logical physical rename)
    (name : String) (source : SequenceSource) (position : Int) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (inside : SourceWithin logical.length source) :
    step module physicalAnchors
        (relocateState rename physical ⟨.block (.reverseSequenceStepLoop name source position body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.block (.reverseSequenceStepLoop name source position body otherwise :: following) env, stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step, sequenceValue_relocate]
  rw [← protectGenerator_relocates]
  congr 1
  by_cases finished : position < 0
  · simp [finished, relocateStep, relocateState, relocateWork]
  · simp only [finished, if_false]
    apply run_readonly_relocates logical physical rename logicalAnchors physicalAnchors
      (Mutable.reversibleSequence (sequenceValue source))
      (Mutable.reversibleSequence (relocateValue rename (sequenceValue source)))
      (List.map (relocateValue rename)) globals
      (fun outcome after executed => reversibleSequence_keeps_heap logical after (sequenceValue source) outcome executed)
      (layout.reversibleSequence (sequenceValue source) inside.value)
    intro items read
    cases item : items[position.toNat]? <;>
      simp [List.getElem?_map, item, relocateStep, relocateState, relocateWork,
        relocateEnv_set, ← loopContinuation_relocate, relocateStmt]

variable (heap : Mutable.Heap) (anchors : Nat)

theorem StateWithin.for_reversed (name : String) (iterable : Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin ⟨.block (.forReversed name iterable body otherwise :: following) env, stack, heap⟩) :
    StepWithin (step module anchors ⟨.block (.forReversed name iterable body otherwise :: following) env, stack, heap⟩ globals) := by
  have loopInside := inside.1.2 _ (List.mem_cons_self ..)
  simp only [StmtWithin] at loopInside
  refine ⟨inside.1.1, ?_⟩
  intro frame member
  rcases List.mem_cons.mp member with rfl | member
  · simp only [FrameWithin]
    exact ⟨inside.1.1, loopInside.1, loopInside.2, fun statement member => inside.1.2 statement (by simp [member])⟩
  · exact inside.2 frame member

theorem StateWithin.reverse_start (name : String) (value : Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (globalsInside : GlobalsWithin heap.length globals)
    (inside : StateWithin ⟨.value value, .reverseSequence name body otherwise following env :: stack, heap⟩) :
    StepWithin (step module anchors ⟨.value value, .reverseSequence name body otherwise following env :: stack, heap⟩ globals) := by
  have saved := inside.2 (.reverseSequence name body otherwise following env) (by simp)
  simp only [FrameWithin] at saved
  simp only [step]
  apply protectGenerator_within
  apply run_readonly_within heap anchors (Mutable.reversibleSequence value) globals globalsInside
    (fun outcome after executed => reversibleSequence_keeps_heap heap after value outcome executed)
  intro items read
  refine ⟨⟨saved.1, ?_⟩, fun frame member => inside.2 frame (by simp [member])⟩
  intro statement member
  rcases List.mem_cons.mp member with rfl | member
  · simp only [StmtWithin]
    exact ⟨sequenceSource_within heap.length value inside.1, saved.2.1, saved.2.2.1⟩
  · exact saved.2.2.2 statement member

theorem StateWithin.reverse_loop (closed : Closed heap)
    (name : String) (source : SequenceSource) (position : Int) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (globalsInside : GlobalsWithin heap.length globals)
    (inside : StateWithin ⟨.block (.reverseSequenceStepLoop name source position body otherwise :: following) env, stack, heap⟩) :
    StepWithin (step module anchors ⟨.block (.reverseSequenceStepLoop name source position body otherwise :: following) env, stack, heap⟩ globals) := by
  have loopInside := inside.1.2 _ (List.mem_cons_self ..)
  have restInside : ∀ statement ∈ following, StmtWithin heap.length statement :=
    fun statement member => inside.1.2 statement (by simp [member])
  have nextInside := loopContinuation_within heap.length body
    (.reverseSequenceStepLoop name source (position - 1) body otherwise) (by simpa only [StmtWithin] using loopInside)
  simp only [StmtWithin] at loopInside
  simp only [step]
  apply protectGenerator_within
  by_cases finished : position < 0
  · simp only [finished, if_true]
    exact ⟨⟨inside.1.1, by
      simpa only [List.mem_append, or_imp, forall_and] using And.intro loopInside.2.2 restInside⟩, inside.2⟩
  · simp only [finished, if_false]
    apply run_readonly_within heap anchors (Mutable.reversibleSequence (sequenceValue source)) globals globalsInside
      (fun outcome after executed => reversibleSequence_keeps_heap heap after (sequenceValue source) outcome executed)
    intro items read
    cases item : items[position.toNat]? with
    | none =>
      exact ⟨⟨inside.1.1, by
        simpa only [List.mem_append, or_imp, forall_and] using And.intro loopInside.2.2 restInside⟩, inside.2⟩
    | some value =>
      have bounded := sequence_items_within heap heap closed (sequenceValue source) items
        (reversibleSequence_sequence heap heap (sequenceValue source) items read) value (List.mem_of_getElem? item)
      exact ⟨⟨inside.1.1.setLocal name value bounded, by
        simpa only [List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq]
          using And.intro (And.intro loopInside.2.1 nextInside) restInside⟩, inside.2⟩

end FormalSW.PyAst.HeapCalls.Relocation
