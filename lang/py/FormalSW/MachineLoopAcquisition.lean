import lang.py.FormalSW.MachineStatementInvariant

/-! Loop acquisition retains live sources and argument effects before cursor execution. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

variable (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
  (logicalAnchors physicalAnchors : Nat)

theorem step_reverse_start_preserves (name : String) (value : Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .reverseSequence name body otherwise following env :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .reverseSequence name body otherwise following env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .reverseSequence name body otherwise following env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · apply protectGenerator_heap
    apply run_readonly_heap
    · exact fun outcome after executed => reversibleSequence_keeps_heap logical after value outcome executed
    · intro _ _; rfl
  · exact StateWithin.reverse_start module logical logicalAnchors name value body otherwise following env stack globals globalsInside inside
  · exact step_reverse_start_relocates module logical physical rename logicalAnchors physicalAnchors layout.runtime
      name value body otherwise following env stack globals inside.1

theorem step_enumerate_source_preserves (index name : String) (value : Value) (start : Expr)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .enumerateSource index name start body otherwise following env :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .enumerateSource index name start body otherwise following env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .enumerateSource index name start body otherwise following env :: stack, logical⟩)
        (relocateGlobals rename globals)) :=
  Preserves.unchanged layout rfl
    (StateWithin.enumerate_source module logical logicalAnchors index name value start body otherwise following env stack globals inside)
    (step_enumerate_source_relocates module logical physical rename logicalAnchors physicalAnchors
      index name value start body otherwise following env stack globals)

theorem step_enumerate_start_preserves (index name : String) (source value : Value)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .enumerateStart index name source body otherwise following env :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .enumerateStart index name source body otherwise following env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .enumerateStart index name source body otherwise following env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have captured := inside.2 (.enumerateStart index name source body otherwise following env) (by simp)
  simp only [FrameWithin] at captured
  apply Preserves.unchanged layout
  · apply protectGenerator_heap
    obtain ⟨outcome, tested⟩ := enumerateStart_total logical value
    cases outcome with
    | error exception => simp [run, tested, done, StepHeap]
    | ok counter =>
      simp only [run, tested]
      apply run_readonly_heap
      · exact fun outcome after executed => sequence_keeps_heap logical after source outcome executed
      · intro _ _; rfl
  · exact StateWithin.enumerate_start module logical logicalAnchors index name source value body otherwise following env stack globals globalsInside inside
  · exact step_enumerate_start_relocates module logical physical rename logicalAnchors physicalAnchors layout.runtime
      index name source value body otherwise following env stack globals captured.1

theorem dictionaryItemsStart_heap (heap : Mutable.Heap) (anchors : Nat) (target : Expr) (receiver : Value)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    StepHeap heap (dictionaryItemsStart anchors target body otherwise following env receiver stack heap globals) := by
  simp only [dictionaryItemsStart]
  repeat' (first | rfl | trivial | split)

theorem step_dictionary_items_start_preserves (target : Expr) (receiver : Value)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value receiver, .dictionaryItemsReceiver target body otherwise following env :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value receiver, .dictionaryItemsReceiver target body otherwise following env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value receiver, .dictionaryItemsReceiver target body otherwise following env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · apply protectGenerator_heap
    exact dictionaryItemsStart_heap logical logicalAnchors target receiver body otherwise following env stack globals
  · exact StateWithin.dictionary_items_start module logical layout.closed logicalAnchors
      target receiver body otherwise following env stack globals globalsInside inside
  · exact step_dictionary_items_start_relocates module logical physical rename logicalAnchors physicalAnchors layout.runtime
      target receiver body otherwise following env stack globals inside.1

theorem dictionaryValuesStart_heap (heap : Mutable.Heap) (anchors : Nat) (target : Expr) (receiver : Value)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    StepHeap heap (dictionaryValuesStart anchors target body otherwise following env receiver stack heap globals) := by
  simp only [dictionaryValuesStart]
  repeat' (first | rfl | trivial | split)

theorem step_dictionary_values_start_preserves (target : Expr) (receiver : Value)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value receiver, .dictionaryValuesReceiver target body otherwise following env :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value receiver, .dictionaryValuesReceiver target body otherwise following env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value receiver, .dictionaryValuesReceiver target body otherwise following env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · apply protectGenerator_heap
    exact dictionaryValuesStart_heap logical logicalAnchors target receiver body otherwise following env stack globals
  · exact StateWithin.dictionary_values_start module logical layout.closed logicalAnchors
      target receiver body otherwise following env stack globals globalsInside inside
  · exact step_dictionary_values_start_relocates module logical physical rename logicalAnchors physicalAnchors layout.runtime
      target receiver body otherwise following env stack globals inside.1

/-- Value continuations that acquire a loop source or finish its argument evaluation. -/
inductive LoopAcquisition : Frame → Prop where
  | sequence (name : String) (body otherwise following : List Stmt) (env : Env) :
      LoopAcquisition (.sequence name body otherwise following env)
  | unpack (names : List String) (body otherwise following : List Stmt) (env : Env) :
      LoopAcquisition (.unpackSequence names body otherwise following env)
  | reverse (name : String) (body otherwise following : List Stmt) (env : Env) :
      LoopAcquisition (.reverseSequence name body otherwise following env)
  | enumerateSource (index name : String) (start : Expr) (body otherwise following : List Stmt) (env : Env) :
      LoopAcquisition (.enumerateSource index name start body otherwise following env)
  | enumerateStart (index name : String) (source : Value) (body otherwise following : List Stmt) (env : Env) :
      LoopAcquisition (.enumerateStart index name source body otherwise following env)
  | dictionaryItems (target : Expr) (body otherwise following : List Stmt) (env : Env) :
      LoopAcquisition (.dictionaryItemsReceiver target body otherwise following env)
  | dictionaryValues (target : Expr) (body otherwise following : List Stmt) (env : Env) :
      LoopAcquisition (.dictionaryValuesReceiver target body otherwise following env)
  | rangeArguments (name : String) (done : List Value) (rest : List Expr) (body otherwise following : List Stmt) (env : Env) :
      LoopAcquisition (.rangeArguments name done rest body otherwise following env)

theorem step_loopAcquisition_preserves (value : Value) (frame : Frame) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename) (acquisition : LoopAcquisition frame)
    (inside : StateWithin ⟨.value value, frame :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, frame :: stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.value value, frame :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases acquisition with
  | sequence => apply step_sequence_start_preserves <;> assumption
  | unpack => apply step_unpack_start_preserves <;> assumption
  | reverse => apply step_reverse_start_preserves <;> assumption
  | enumerateSource => apply step_enumerate_source_preserves <;> assumption
  | enumerateStart => apply step_enumerate_start_preserves <;> assumption
  | dictionaryItems => apply step_dictionary_items_start_preserves <;> assumption
  | dictionaryValues => apply step_dictionary_values_start_preserves <;> assumption
  | rangeArguments => apply step_range_arguments_preserves <;> assumption

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_loopAcquisition_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (value : Mutable.Value) (frame : HeapCalls.Frame) (stack : List HeapCalls.Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module)
    (layout : ExecutionLayout logical physical rename) (acquisition : LoopAcquisition frame)
    (inside : StateWithin logical.length (.running ⟨⟨.value value, frame :: stack, logical⟩, used⟩ resumes))
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices (.running ⟨⟨.value value, frame :: stack, logical⟩, used⟩ resumes) globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.running ⟨⟨.value value, frame :: stack, logical⟩, used⟩ resumes))
        (relocateGlobals rename globals)) := by
  apply step_preserves module choices (.running ⟨⟨.value value, frame :: stack, logical⟩, used⟩ resumes)
    logical physical rename logicalAnchors physicalAnchors globals source layout rfl inside globalsInside
  intro core pending same _
  cases same
  exact SetCalls.Relocation.step_preserves_of_heap module choices _ physical rename logicalAnchors physicalAnchors
    globals layout ⟨inside.1, inside.2.1⟩ globalsInside
    (HeapCalls.Relocation.step_loopAcquisition_preserves module logical physical rename logicalAnchors physicalAnchors
      value frame stack globals layout acquisition ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
