import lang.py.FormalSW.BufferCost

/-! Exact weighted cost of a successful, length-preserving bytearray slice write.
The operation is the real heap-interpreter transition; equal old/new contents do
not remove the charge for writing replacement bytes. -/
namespace FormalSW.PyAst.HeapCalls.BufferCost

theorem bufferSlots_set_same_length (heap : Heap) (address : Nat) (before after : List UInt8)
    (found : heap[address]? = some (.bytearray before)) (length : after.length = before.length) :
    bufferSlots (heap.set address (.bytearray after)) = bufferSlots heap := by
  induction heap generalizing address with
  | nil => simp at found
  | cons head tail ih =>
      cases address with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst head
          simp [bufferSlots, length]
      | succ address =>
          simp only [List.getElem?_cons_succ] at found
          simpa only [bufferSlots, List.set, List.map_cons, List.sum_cons] using
            congrArg ((match head with | .bytearray bytes => bytes.length | _ => 0) + ·) (ih address found)

theorem slice_charge (module : Module) (anchors : Nat) (stack : List Frame)
    (heap : Heap) (address : Nat) (before after replacement : List UInt8)
    (lower upper stride : Value)
    (found : heap[address]? = some (.bytearray before)) (length : after.length = before.length)
    (write : Mutable.setSlice (.ref address) lower upper stride (.scalar (.bytes replacement)) heap =
      some (.ok (.scalar .none), heap.set address (.bytearray after))) :
    charge module anchors
      ⟨.operation (.setSlice (.scalar (.bytes replacement))) [.ref address, lower, upper, stride], stack, heap⟩ =
      1 + replacement.length := by
  have transition : step module anchors
      ⟨.operation (.setSlice (.scalar (.bytes replacement))) [.ref address, lower, upper, stride], stack, heap⟩ =
      .next ⟨.value (.scalar .none), stack, heap.set address (.bytearray after)⟩ := by
    simp [step, primitive, result, run, write]
  simp [charge, transition, bufferSlots_set_same_length heap address before after found length,
    scalarBytes, writtenBytes, isBuffer, byteLength, found]

end FormalSW.PyAst.HeapCalls.BufferCost
