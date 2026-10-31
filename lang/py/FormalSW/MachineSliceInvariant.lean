import lang.py.FormalSW.SliceRelocation
import lang.py.FormalSW.ByteValuesRelocation
import lang.py.FormalSW.MachineSequenceConstruction

/-! Slice operations preserve argument effects, shallow aliases and exact failure states. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem result_allocateBuffer_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (items : List UInt8) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (Mutable.allocateBuffer items) stack globals)
      (result physicalAnchors physical (Mutable.allocateBuffer items)
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  obtain ⟨left, right, retained⟩ := layout.allocateBuffer items
  apply result_preserves logical physical _ _ rename (extendMap rename logical.length physical.length)
    logicalAnchors physicalAnchors _ _ stack globals (.ok (.ref logical.length))
    (extendMap_old _ _ _) (by simp) (by simp) retained stackInside globalsInside
  · intro value same; cases same; simp [Mutable.Value.edge, Graph.Edge.Within]
  · exact left
  · simpa only [Except.map, relocateValue, extendMap_new] using right


theorem result_sliceBounds_bind_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (lower upper stride : Value)
    (next otherNext : Py.Builtin.Slice.Slice → Mutable.Eval Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (globalsInside : GlobalsWithin logical.length globals)
    (continues : ∀ bounds,
      Preserves logical physical rename physicalAnchors
        (result logicalAnchors logical (next bounds) stack globals)
        (result physicalAnchors physical (otherNext bounds) (stack.map (relocateFrame rename)) (relocateGlobals rename globals))) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (Mutable.sliceBounds lower upper stride >>= next) stack globals)
      (result physicalAnchors physical
        (Mutable.sliceBounds (relocateValue rename lower) (relocateValue rename upper) (relocateValue rename stride) >>= otherNext)
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  rw [result_bind, result_bind]
  apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _ id _ _ globals layout globalsInside
    (fun outcome after executed => sliceBounds_heap logical after lower upper stride outcome executed)
    (by simpa only [Except.map_id] using sliceBounds_relocates logical physical rename lower upper stride)
  exact fun bounds _ => continues bounds

theorem result_sliceResult_bind_preserves {α β : Type} (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (outcome : Py.Builtin.Result α) (move : α → β)
    (next : α → Mutable.Eval Value) (otherNext : β → Mutable.Eval Value)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (globalsInside : GlobalsWithin logical.length globals)
    (continues : ∀ value, outcome = .ok value →
      Preserves logical physical rename physicalAnchors
        (result logicalAnchors logical (next value) stack globals)
        (result physicalAnchors physical (otherNext (move value)) (stack.map (relocateFrame rename)) (relocateGlobals rename globals))) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (sliceResult outcome >>= next) stack globals)
      (result physicalAnchors physical (sliceResult (outcome.map move) >>= otherNext)
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  rw [result_bind, result_bind]
  apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _ move _ _ globals layout globalsInside
    (fun answer after executed => sliceResult_heap logical after outcome answer executed)
    (sliceResult_relocates move outcome logical physical)
  exact fun value executed => continues value (sliceResult_ok logical outcome value executed)

def readSliceObject (address : Nat) (object : Mutable.Object) (bounds : Py.Builtin.Slice.Slice) : Mutable.Eval Value :=
  match object with
  | .list items => do Mutable.allocate (← sliceResult (Py.Builtin.Sequence.slice items bounds))
  | .tuple items => do
      let normalized ← sliceResult (Py.Builtin.Slice.indices bounds items.length)
      if normalized = (0, (items.length : Int), 1) then pure (.ref address)
      else Mutable.allocateTuple (← sliceResult (Py.Builtin.Sequence.slice items bounds))
  | .bytearray bytes => do Mutable.allocateBuffer (← sliceResult (Py.Builtin.Sequence.slice bytes bounds))
  | _ => Mutable.unsupported

theorem result_readSliceObject_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (address : Nat) (object : Mutable.Object) (bounds : Py.Builtin.Slice.Slice)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (found : logical[address]? = some object) (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (readSliceObject address object bounds) stack globals)
      (result physicalAnchors physical (readSliceObject (rename address) (relocateObject rename object) bounds)
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  have itemsInside := layout.closed object (List.mem_of_getElem? found)
  cases object with
  | list items =>
    simp only [readSliceObject, relocateObject, slice_map]
    apply result_sliceResult_bind_preserves logical physical rename logicalAnchors physicalAnchors _ _ _ _ stack globals layout globalsInside
    intro selected sliced
    exact result_allocateList_preserves logical physical rename logicalAnchors physicalAnchors selected stack globals layout
      (fun value member => itemsInside value (slice_mem items selected bounds sliced value member)) stackInside globalsInside
  | tuple items =>
    simp only [readSliceObject, relocateObject, List.length_map]
    have same : Py.Builtin.Slice.indices bounds items.length = (Py.Builtin.Slice.indices bounds items.length).map id := by
      simp
    conv => rhs; rw [same]
    apply result_sliceResult_bind_preserves logical physical rename logicalAnchors physicalAnchors _ id _ _ stack globals layout globalsInside
    intro normalized _
    dsimp only [id]
    by_cases full : normalized = (0, (items.length : Int), 1)
    · simp only [full, if_true]
      exact result_pure_preserves logical physical rename logicalAnchors physicalAnchors (.ref address) stack globals layout
        (List.getElem?_eq_some_iff.mp found).1 stackInside
    · simp only [full, if_false, slice_map]
      apply result_sliceResult_bind_preserves logical physical rename logicalAnchors physicalAnchors _ _ _ _ stack globals layout globalsInside
      intro selected sliced
      exact result_allocateTuple_preserves logical physical rename logicalAnchors physicalAnchors selected stack globals layout
        (fun value member => itemsInside value (slice_mem items selected bounds sliced value member)) stackInside globalsInside
  | bytearray bytes =>
    simp only [readSliceObject, relocateObject]
    have same : Py.Builtin.Sequence.slice bytes bounds = (Py.Builtin.Sequence.slice bytes bounds).map id := by simp
    conv => rhs; rw [same]
    apply result_sliceResult_bind_preserves logical physical rename logicalAnchors physicalAnchors _ id _ _ stack globals layout globalsInside
    intro selected _
    exact result_allocateBuffer_preserves logical physical rename logicalAnchors physicalAnchors selected stack globals layout stackInside globalsInside
  | dict entries | keyDict entries | set items | keySet items
  | «instance» origin name fields | dataInstance origin name frozen declared fields =>
    exact Preserves.unchanged layout (by trivial) (by trivial) rfl

theorem getSlice_ref (heap : Mutable.Heap) (address : Nat) (object : Mutable.Object) (lower upper stride : Value)
    (found : heap[address]? = some object) :
    Mutable.getSlice (.ref address) lower upper stride heap =
      (match object with
      | .list _ | .tuple _ | .bytearray _ => Mutable.sliceBounds lower upper stride >>= readSliceObject address object
      | .dict _ | .keyDict _ => Mutable.unsupported
      | _ => Mutable.error "TypeError") heap := by
  cases object <;> simp [Mutable.getSlice, found, readSliceObject] <;> rfl

theorem result_getSlice_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (receiver lower upper stride : Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (receiverInside : receiver.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (Mutable.getSlice receiver lower upper stride) stack globals)
      (result physicalAnchors physical
        (Mutable.getSlice (relocateValue rename receiver) (relocateValue rename lower) (relocateValue rename upper) (relocateValue rename stride))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  cases receiver with
  | scalar scalar =>
    cases scalar with
    | string text =>
      apply result_sliceBounds_bind_preserves logical physical rename logicalAnchors physicalAnchors lower upper stride _ _ stack globals layout globalsInside
      intro bounds
      let encode := fun (bound : Option Int) => (bound.map Constant.int).getD .none
      have preserved := result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (Strings.slice (.string text) (encode bounds.start) (encode bounds.stop) (encode bounds.step))) stack globals layout stackInside globalsInside
      cases outcome : Strings.slice (.string text) (encode bounds.start) (encode bounds.stop) (encode bounds.step) <;>
        simpa only [scalarResult, encode, outcome] using preserved
    | bytes bytes =>
      apply result_sliceBounds_bind_preserves logical physical rename logicalAnchors physicalAnchors lower upper stride _ _ stack globals layout globalsInside
      intro bounds
      let encode := fun (bound : Option Int) => (bound.map Constant.int).getD .none
      have preserved := result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (Strings.slice (.bytes bytes) (encode bounds.start) (encode bounds.stop) (encode bounds.step))) stack globals layout stackInside globalsInside
      cases outcome : Strings.slice (.bytes bytes) (encode bounds.start) (encode bounds.stop) (encode bounds.step) <;>
        simpa only [scalarResult, encode, outcome] using preserved
    | int number | bool value | none =>
      exact result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (.error ⟨"TypeError", []⟩)) stack globals layout stackInside globalsInside
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem receiverInside
    have moved := layout.runtime.lookup address _ found
    cases object : logical[address] <;> simp only [object, relocateObject] at moved
    all_goals
      simp only [result, run, relocateValue, getSlice_ref logical address _ _ _ _ (found.trans (congrArg some object)),
        getSlice_ref physical (rename address) _ _ _ _ moved]
    case list items | tuple items | bytearray bytes =>
      apply result_sliceBounds_bind_preserves logical physical rename logicalAnchors physicalAnchors lower upper stride _ _ stack globals layout globalsInside
      intro bounds
      exact result_readSliceObject_preserves logical physical rename logicalAnchors physicalAnchors address _ bounds stack globals layout
        (found.trans (congrArg some object)) stackInside globalsInside
    case dict entries | keyDict entries => exact Preserves.unchanged layout (by trivial) (by trivial) rfl
    all_goals
      exact result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (.error ⟨"TypeError", []⟩)) stack globals layout stackInside globalsInside

def storeSliceObject (address : Nat) (object : Mutable.Object) : Mutable.Eval Value := do
  modify fun heap => heap.set address object
  pure (.scalar .none)

theorem result_storeSliceObject_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (address : Nat) (before after : Mutable.Object)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (found : logical[address]? = some before) (oldTuple : before ≠ .tuple []) (newTuple : after ≠ .tuple [])
    (bounded : ObjectWithin logical.length after) (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (storeSliceObject address after) stack globals)
      (result physicalAnchors physical (storeSliceObject (rename address) (relocateObject rename after))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  have retained := layout.set_nonempty address before after found oldTuple newTuple bounded
  apply result_preserves logical physical _ _ rename rename logicalAnchors physicalAnchors _ _ stack globals (.ok (.scalar .none))
    (fun _ _ => rfl) (by simp) (by simp) retained stackInside globalsInside
  · intro value same; cases same; trivial
  · rfl
  · rfl

def writeSliceObject (address : Nat) (object : Mutable.Object) (replacement : Value)
    (bounds : Py.Builtin.Slice.Slice) : Mutable.Eval Value :=
  match object with
  | .list items => do
      let values ← Mutable.sequence replacement
      let updated ← sliceResult (Py.Builtin.List.setSlice items bounds values)
      storeSliceObject address (.list updated)
  | .bytearray bytes => do
      let values ← Mutable.byteValues replacement
      let updated ← sliceResult (Py.Builtin.ByteArray.setSlice bytes bounds values)
      storeSliceObject address (.bytearray updated)
  | _ => Mutable.unsupported

theorem result_writeSliceObject_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (address : Nat) (object : Mutable.Object) (replacement : Value)
    (bounds : Py.Builtin.Slice.Slice) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (found : logical[address]? = some object)
    (replacementInside : replacement.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (writeSliceObject address object replacement bounds) stack globals)
      (result physicalAnchors physical
        (writeSliceObject (rename address) (relocateObject rename object) (relocateValue rename replacement) bounds)
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  cases object with
  | list items =>
    simp only [writeSliceObject, relocateObject]
    conv => lhs; rw [result_bind]
    conv => rhs; rw [result_bind]
    apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _ (List.map (relocateValue rename)) _ _ globals layout globalsInside
      (fun outcome after executed => sequence_keeps_heap logical after replacement outcome executed)
      (layout.runtime.sequence replacement replacementInside)
    intro values read
    have old := layout.closed (.list items) (List.mem_of_getElem? found)
    have new := sequence_items_within logical logical layout.closed replacement values read
    simp only [setSlice_map]
    apply result_sliceResult_bind_preserves logical physical rename logicalAnchors physicalAnchors _ _ _ _ stack globals layout globalsInside
    intro updated written
    exact result_storeSliceObject_preserves logical physical rename logicalAnchors physicalAnchors address (.list items) (.list updated)
      stack globals layout found (by simp) (by simp)
      (setSlice_within (fun value : Value => value.edge.Within logical.length) items values updated bounds old new written)
      stackInside globalsInside
  | bytearray bytes =>
    simp only [writeSliceObject, relocateObject]
    conv => lhs; rw [result_bind]
    conv => rhs; rw [result_bind]
    apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _ id _ _ globals layout globalsInside
      (fun outcome after executed => byteValues_heap logical after replacement outcome executed)
      (by simpa only [Except.map_id] using layout.runtime.byteValues replacement replacementInside)
    intro values _
    dsimp only [id]
    have same : Py.Builtin.ByteArray.setSlice bytes bounds values = (Py.Builtin.ByteArray.setSlice bytes bounds values).map id := by simp
    conv => rhs; rw [same]
    apply result_sliceResult_bind_preserves logical physical rename logicalAnchors physicalAnchors _ id _ _ stack globals layout globalsInside
    intro updated _
    exact result_storeSliceObject_preserves logical physical rename logicalAnchors physicalAnchors address (.bytearray bytes) (.bytearray updated)
      stack globals layout found (by simp) (by simp) (by simp [ObjectWithin, objectValues]) stackInside globalsInside
  | tuple items | dict entries | keyDict entries | set items | keySet items
  | «instance» origin name fields | dataInstance origin name frozen declared fields =>
    exact Preserves.unchanged layout (by trivial) (by trivial) rfl

theorem setSlice_ref (heap : Mutable.Heap) (address : Nat) (object : Mutable.Object) (lower upper stride replacement : Value)
    (found : heap[address]? = some object) :
    Mutable.setSlice (.ref address) lower upper stride replacement heap =
      (match object with
      | .list _ | .bytearray _ => Mutable.sliceBounds lower upper stride >>= writeSliceObject address object replacement
      | .dict _ | .keyDict _ => Mutable.unsupported
      | _ => Mutable.error "TypeError") heap := by
  cases object <;> simp [Mutable.setSlice, found, writeSliceObject, storeSliceObject] <;> rfl

theorem result_setSlice_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (receiver lower upper stride replacement : Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (receiverInside : receiver.edge.Within logical.length)
    (replacementInside : replacement.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (Mutable.setSlice receiver lower upper stride replacement) stack globals)
      (result physicalAnchors physical
        (Mutable.setSlice (relocateValue rename receiver) (relocateValue rename lower) (relocateValue rename upper)
          (relocateValue rename stride) (relocateValue rename replacement))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  cases receiver with
  | scalar scalar =>
    exact result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
      (some (.error ⟨"TypeError", []⟩)) stack globals layout stackInside globalsInside
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem receiverInside
    have moved := layout.runtime.lookup address _ found
    cases object : logical[address] <;> simp only [object, relocateObject] at moved
    all_goals
      simp only [result, run, relocateValue, setSlice_ref logical address _ _ _ _ _ (found.trans (congrArg some object)),
        setSlice_ref physical (rename address) _ _ _ _ _ moved]
    case list items | bytearray bytes =>
      apply result_sliceBounds_bind_preserves logical physical rename logicalAnchors physicalAnchors lower upper stride _ _ stack globals layout globalsInside
      intro bounds
      exact result_writeSliceObject_preserves logical physical rename logicalAnchors physicalAnchors address _ replacement bounds stack globals layout
        (found.trans (congrArg some object)) replacementInside stackInside globalsInside
    case dict entries | keyDict entries => exact Preserves.unchanged layout (by trivial) (by trivial) rfl
    all_goals
      exact result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (.error ⟨"TypeError", []⟩)) stack globals layout stackInside globalsInside

inductive SliceOperation : Operation → Prop
  | read : SliceOperation .slice
  | write (replacement : Value) : SliceOperation (.setSlice replacement)

theorem step_slice_preserves (module : Module)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (operation : Operation) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (covered : SliceOperation operation)
    (inside : StateWithin ⟨.operation operation values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation operation values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation operation values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases covered with
  | read =>
    rcases values with _ | ⟨receiver, _ | ⟨lower, _ | ⟨upper, _ | ⟨stride, _ | ⟨extra, rest⟩⟩⟩⟩⟩
    case cons.cons.cons.cons.nil =>
      exact (result_getSlice_preserves logical physical rename logicalAnchors physicalAnchors receiver lower upper stride stack globals
        layout (inside.1.2 receiver (by simp)) inside.2 globalsInside).protectGenerator stack inside.2
    all_goals exact Preserves.unchanged layout (by trivial) (by trivial) rfl
  | write replacement =>
    rcases values with _ | ⟨receiver, _ | ⟨lower, _ | ⟨upper, _ | ⟨stride, _ | ⟨extra, rest⟩⟩⟩⟩⟩
    case cons.cons.cons.cons.nil =>
      exact (result_setSlice_preserves logical physical rename logicalAnchors physicalAnchors receiver lower upper stride replacement stack globals
        layout (inside.1.2 receiver (by simp)) inside.1.1 inside.2 globalsInside).protectGenerator stack inside.2
    all_goals exact Preserves.unchanged layout (by trivial) (by trivial) rfl

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_slice_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (operation : Operation) (values : List Mutable.Value) (stack : List Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (covered : SliceOperation operation)
    (inside : StateWithin logical.length (.running ⟨⟨.operation operation values, stack, logical⟩, used⟩ resumes))
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices (.running ⟨⟨.operation operation values, stack, logical⟩, used⟩ resumes) globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.running ⟨⟨.operation operation values, stack, logical⟩, used⟩ resumes))
        (relocateGlobals rename globals)) := by
  apply step_preserves module choices (.running ⟨⟨.operation operation values, stack, logical⟩, used⟩ resumes)
    logical physical rename logicalAnchors physicalAnchors globals source layout rfl inside globalsInside
  intro core pending same _
  cases same
  exact SetCalls.Relocation.step_preserves_of_heap module choices _ physical rename logicalAnchors physicalAnchors
    globals layout ⟨inside.1, inside.2.1⟩ globalsInside
    (HeapCalls.Relocation.step_slice_preserves module logical physical rename logicalAnchors physicalAnchors
      operation values stack globals layout covered ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
