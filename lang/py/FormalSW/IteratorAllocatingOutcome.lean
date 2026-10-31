import lang.py.FormalSW.IteratorExecutionIsolation
import lang.py.FormalSW.DictionaryAllocation
import lang.py.FormalSW.SequenceAllocation
import lang.py.FormalSW.BufferAllocation
import lang.py.FormalSW.BufferArithmeticAllocation
import lang.py.FormalSW.SetArithmeticAllocation
import lang.py.FormalSW.SequenceArithmeticAllocation

/-! Allocating operations retain their heap on success and on ordinary exceptions. -/
namespace FormalSW.PyAst.IteratorCalls
open HeapCalls HeapCalls.Relocation Mutable.Relocation
set_option Elab.async false

def allocationResult (anchors used : Nat) (globals : Mutable.Globals) (heap : Mutable.Heap)
    (stack : List Frame) (resumes : List Resume) : Except ExceptionObject Mutable.Value → State
  | .ok value => .running ⟨⟨.value value, stack, heap⟩, used⟩ resumes
  | .error error => .completed
      (.ok ⟨.error (Calls.generatorException (stack.any Frame.inGenerator) error), globals, heap, anchors⟩) used resumes

theorem allocationResult_within (anchors used : Nat) (globals : Mutable.Globals) (heap : Mutable.Heap)
    (stack : List Frame) (resumes : List Resume) (outcome : Except ExceptionObject Mutable.Value)
    (returned : ∀ value, outcome = .ok value → value.edge.Within heap.length)
    (globalsInside : GlobalsWithin heap.length globals)
    (stackInside : ∀ frame ∈ stack, FrameWithin heap.length frame)
    (saved : ∀ pending ∈ resumes, Relocation.ResumeWithin heap.length pending) :
    Relocation.StateWithin heap.length (allocationResult anchors used globals heap stack resumes outcome) := by
  cases outcome with
  | ok value => exact ⟨returned value rfl, stackInside, saved⟩
  | error error => exact ⟨globalsInside, (by intro value impossible; cases impossible), saved⟩

theorem allocationResult_relocates (rename : Nat → Nat) (logical physical : Mutable.Heap)
    (logicalAnchors physicalAnchors used : Nat) (globals : Mutable.Globals)
    (stack : List Frame) (resumes : List Resume) (outcome : Except ExceptionObject Mutable.Value) :
    Relocation.relocateState rename physical physicalAnchors
      (allocationResult logicalAnchors used globals logical stack resumes outcome) =
    allocationResult physicalAnchors used (relocateGlobals rename globals) physical
      (stack.map (relocateFrame rename)) (resumes.map (Relocation.relocateResume rename))
      (outcome.map (relocateValue rename)) := by
  cases outcome <;> simp only [allocationResult, Relocation.relocateState, Relocation.relocateCore,
    HeapCalls.Relocation.relocateState, relocateWork, relocateCompletion, Except.map, relocateStack_inGenerator]

theorem setDisplay_step (module : Module) (anchors used : Nat) (choices : ChoiceSchedule)
    (globals : Mutable.Globals) (heap after : Mutable.Heap) (items : List Mutable.Value)
    (stack : List Frame) (resumes : List Resume) (outcome : Except ExceptionObject Mutable.Value)
    (allocated : Mutable.allocateSetValues items heap = some (outcome, after)) :
    step module anchors choices (.running ⟨⟨.operation (.builtin .setDisplay) items, stack, heap⟩, used⟩ resumes) globals =
      .next (allocationResult anchors used globals after stack resumes outcome) := by
  cases outcome <;> simp [step, intercept, SetCalls.step, HeapCalls.step, primitive,
    result, run, allocated, protectGenerator, done, SetCalls.liftStep, lift, allocationResult]

/-- Set displays use their evaluated items; constructors first collect a supported source. -/
inductive SetAllocationInput (heap : Mutable.Heap) : Builtin → List Mutable.Value → List Mutable.Value → Prop where
  | display (items : List Mutable.Value) : SetAllocationInput heap .setDisplay items items
  | empty : SetAllocationInput heap .set [] []
  | source (value : Mutable.Value) (items : List Mutable.Value)
      (read : setSourceItems value heap = some (.ok items, heap)) : SetAllocationInput heap .set [value] items

theorem SetAllocationInput.within {heap : Mutable.Heap} {builtin : Builtin} {values items : List Mutable.Value}
    (input : SetAllocationInput heap builtin values items) (closed : Closed heap)
    (inside : ∀ value ∈ values, value.edge.Within heap.length) :
    ∀ value ∈ items, value.edge.Within heap.length := by
  cases input with
  | display => exact inside
  | empty => simp
  | source value items read => exact setSourceItems_bounded heap closed value (inside value (by simp)) items read

theorem SetAllocationInput.relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    {builtin : Builtin} {values items : List Mutable.Value}
    (input : SetAllocationInput logical builtin values items) (layout : ExecutionLayout logical physical rename)
    (inside : ∀ value ∈ values, value.edge.Within logical.length) :
    SetAllocationInput physical builtin (values.map (relocateValue rename)) (items.map (relocateValue rename)) := by
  cases input with
  | display => exact .display _
  | empty => exact .empty
  | source value items read =>
      apply SetAllocationInput.source
      have moved := layout.runtime.setSourceItems value (inside value (by simp))
      simpa only [read, Option.map, Except.map] using moved

theorem setAllocation_step (module : Module) (anchors used : Nat) (choices : ChoiceSchedule)
    (globals : Mutable.Globals) (heap after : Mutable.Heap) (builtin : Builtin) (values items : List Mutable.Value)
    (stack : List Frame) (resumes : List Resume) (outcome : Except ExceptionObject Mutable.Value)
    (input : SetAllocationInput heap builtin values items)
    (allocated : Mutable.allocateSetValues items heap = some (outcome, after)) :
    step module anchors choices (.running ⟨⟨.operation (.builtin builtin) values, stack, heap⟩, used⟩ resumes) globals =
      .next (allocationResult anchors used globals after stack resumes outcome) := by
  cases input with
  | display => exact setDisplay_step module anchors used choices globals heap after _ stack resumes outcome allocated
  | empty =>
      change Mutable.allocateSet [] heap = some (outcome, after) at allocated
      cases outcome <;> simp [step, intercept, SetCalls.step, HeapCalls.step, primitive,
        result, run, allocated, protectGenerator, done, SetCalls.liftStep, lift, allocationResult]
  | source value items read =>
      have ran : Mutable.setFrom value heap = some (outcome, after) := by
        simpa [setFrom_eq, read, Mutable.eval_bind] using allocated
      cases outcome <;> simp [step, intercept, SetCalls.step, HeapCalls.step, primitive,
        result, run, ran, protectGenerator, done, SetCalls.liftStep, lift, allocationResult]

theorem dictionaryConstruct_step (module : Module) (anchors used : Nat) (choices : ChoiceSchedule)
    (globals : Mutable.Globals) (heap after : Mutable.Heap) (values : List Mutable.Value)
    (stack : List Frame) (resumes : List Resume) (outcome : Except ExceptionObject Mutable.Value)
    (allocated : DictionaryConstructor.construct values heap = some (outcome, after)) :
    step module anchors choices (.running ⟨⟨.operation (.builtin .dict) values, stack, heap⟩, used⟩ resumes) globals =
      .next (allocationResult anchors used globals after stack resumes outcome) := by
  cases outcome <;> simp [step, intercept, SetCalls.step, HeapCalls.step, primitive,
    result, run, allocated, protectGenerator, done, SetCalls.liftStep, lift, allocationResult]

theorem sequenceAllocation_step (module : Module) (anchors used : Nat) (choices : ChoiceSchedule)
    (globals : Mutable.Globals) (heap after : Mutable.Heap) (operation : Operation)
    (values items : List Mutable.Value) (asTuple : Bool) (address : Nat) (stack : List Frame) (resumes : List Resume)
    (input : SequenceAllocationInput heap operation values asTuple items)
    (allocated : allocateSequence asTuple items heap = some (.ok (.ref address), after)) :
    step module anchors choices (.running ⟨⟨.operation operation values, stack, heap⟩, used⟩ resumes) globals =
      .next (.running ⟨⟨.value (.ref address), stack, after⟩, used⟩ resumes) := by
  have ran := input.primitive.trans allocated
  cases input <;> apply core_next rfl <;>
    simp [SetCalls.step, SetCalls.liftStep, HeapCalls.step, result, run, ran]

theorem bufferAllocation_step (module : Module) (anchors used : Nat) (choices : ChoiceSchedule)
    (globals : Mutable.Globals) (heap : Mutable.Heap) (operation : Operation) (values : List Mutable.Value)
    (bytes : List UInt8) (stack : List Frame) (resumes : List Resume)
    (input : BufferAllocationInput heap operation values bytes) :
    step module anchors choices (.running ⟨⟨.operation operation values, stack, heap⟩, used⟩ resumes) globals =
      .next (.running ⟨⟨.value (.ref heap.length), stack, heap ++ [.bytearray bytes]⟩, used⟩ resumes) := by
  have ran := input.primitive
  cases input <;> apply core_next rfl <;>
    simp [SetCalls.step, SetCalls.liftStep, HeapCalls.step, result, run, ran]

theorem sequenceArithmetic_step (module : Module) (anchors used : Nat) (choices : ChoiceSchedule)
    (globals : Mutable.Globals) (heap after : Mutable.Heap) (op : BinOp) (left right : Mutable.Value)
    (asTuple : Bool) (items : List Mutable.Value) (address : Nat) (stack : List Frame) (resumes : List Resume)
    (input : SequenceArithmeticInput heap op left right asTuple items)
    (allocated : allocateSequence asTuple items heap = some (.ok (.ref address), after)) :
    step module anchors choices (.running ⟨⟨.value right, .binaryRight op left false :: stack, heap⟩, used⟩ resumes) globals =
      .next (.running ⟨⟨.value (.ref address), stack, after⟩, used⟩ resumes) := by
  have ran := input.binary.trans allocated
  apply core_next rfl
  simp [SetCalls.step, SetCalls.liftStep, HeapCalls.step, result, run, ran]

theorem bufferArithmetic_step (module : Module) (anchors used : Nat) (choices : ChoiceSchedule)
    (globals : Mutable.Globals) (heap : Mutable.Heap) (op : BinOp) (left right : Mutable.Value)
    (bytes : List UInt8) (stack : List Frame) (resumes : List Resume)
    (input : BufferArithmeticInput heap op left right bytes) :
    step module anchors choices (.running ⟨⟨.value right, .binaryRight op left false :: stack, heap⟩, used⟩ resumes) globals =
      .next (.running ⟨⟨.value (.ref heap.length), stack, heap ++ [.bytearray bytes]⟩, used⟩ resumes) := by
  have ran := input.binary
  apply core_next rfl
  simp [SetCalls.step, SetCalls.liftStep, HeapCalls.step, result, run, ran]

theorem setArithmetic_step (module : Module) (anchors used : Nat) (choices : ChoiceSchedule)
    (globals : Mutable.Globals) (heap : Mutable.Heap) (op : BinOp) (left right : Mutable.Value)
    (items : List Constant) (stack : List Frame) (resumes : List Resume)
    (input : SetArithmeticInput heap op left right items) :
    step module anchors choices (.running ⟨⟨.value right, .binaryRight op left false :: stack, heap⟩, used⟩ resumes) globals =
      .next (.running ⟨⟨.value (.ref heap.length), stack, heap ++ [.set items]⟩, used⟩ resumes) := by
  have ran := input.binary
  apply core_next rfl
  simp [SetCalls.step, SetCalls.liftStep, HeapCalls.step, result, run, ran]

end FormalSW.PyAst.IteratorCalls
