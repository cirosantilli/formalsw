import lang.py.FormalSW.MachineBufferConstruction
import lang.py.FormalSW.ConstructionIsolation

/-! Successful bytearray construction and slicing allocate fresh buffers after validating their inputs. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

inductive BufferAllocationInput (heap : Mutable.Heap) : Operation → List Value → List UInt8 → Prop where
  | empty : BufferAllocationInput heap (.builtin .bytearray) [] []
  | count (size : Int) (nonnegative : 0 ≤ size) :
      BufferAllocationInput heap (.builtin .bytearray) [.scalar (.int size)] (List.replicate size.toNat 0)
  | flag (value : Bool) :
      BufferAllocationInput heap (.builtin .bytearray) [.scalar (.bool value)] (if value then [0] else [])
  | source (value : Value) (bytes : List UInt8)
      (read : Mutable.byteValues value heap = some (.ok bytes, heap)) :
      BufferAllocationInput heap (.builtin .bytearray) [value] bytes
  | slice (address : Nat) (original selected : List UInt8) (lower upper stride : Value)
      (bounds : Py.Builtin.Slice.Slice)
      (found : heap[address]? = some (.bytearray original))
      (coordinates : sliceCoordinates lower upper stride = .ok bounds)
      (sliced : Py.Builtin.Sequence.slice original bounds = .ok selected) :
      BufferAllocationInput heap .slice [.ref address, lower, upper, stride] selected

theorem BufferAllocationInput.relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    {operation : Operation} {values : List Value} {bytes : List UInt8}
    (input : BufferAllocationInput logical operation values bytes) (layout : ExecutionLayout logical physical rename)
    (inside : ∀ value ∈ values, value.edge.Within logical.length) :
    BufferAllocationInput physical operation (values.map (relocateValue rename)) bytes := by
  cases input with
  | empty => exact .empty
  | count size nonnegative => exact .count size nonnegative
  | flag value => exact .flag value
  | source value bytes read =>
    apply BufferAllocationInput.source
    simpa only [read, Option.map] using layout.runtime.byteValues value (inside value (by simp))
  | slice address original selected lower upper stride bounds found coordinates sliced =>
    apply BufferAllocationInput.slice (rename address) original bytes _ _ _ bounds
    · simpa only [relocateObject] using layout.runtime.lookup address _ found
    · simpa only [sliceCoordinates_relocates] using coordinates
    · exact sliced

theorem BufferAllocationInput.operation_relocates {heap : Mutable.Heap} {operation : Operation}
    {values : List Value} {bytes : List UInt8} (input : BufferAllocationInput heap operation values bytes)
    (rename : Nat → Nat) : relocateRuntimeOperation rename operation = operation := by
  cases input <;> rfl

theorem BufferAllocationInput.primitive {heap : Mutable.Heap} {operation : Operation}
    {values : List Value} {bytes : List UInt8} (input : BufferAllocationInput heap operation values bytes) :
    HeapCalls.primitive operation values heap = some (.ok (.ref heap.length), heap ++ [.bytearray bytes]) := by
  cases input with
  | empty => rfl
  | count size nonnegative =>
    simp [HeapCalls.primitive, Mutable.bytearray, show ¬ size < 0 by omega, Mutable.allocateBuffer, Except.map]
  | flag value => cases value <;> rfl
  | source value bytes read =>
    cases value with
    | ref address => simp [HeapCalls.primitive, Mutable.bytearray, Mutable.eval_bind, read, Mutable.allocateBuffer, Except.map]
    | scalar value =>
      cases value <;> simp [Mutable.byteValues, Mutable.error] at read
      case bytes original =>
        subst bytes
        rfl
  | slice address original selected lower upper stride bounds found coordinates sliced =>
    change Mutable.getSlice (.ref address) lower upper stride heap = _
    rw [getSlice_ref heap address _ lower upper stride found]
    simp [sliceBounds_result, coordinates, readSliceObject, sliced, sliceResult, Mutable.eval_bind, Mutable.allocateBuffer, Except.map]

end FormalSW.PyAst.HeapCalls.Relocation
