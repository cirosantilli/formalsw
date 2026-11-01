import lang.py.FormalSW.CompositeHeapFrame
import lang.py.FormalSW.BinaryEffects

/-! Binary operators preserve unrelated cells through allocation and in-place updates. -/
namespace FormalSW.PyAst.Heapq
open Mutable Mutable.Relocation HeapCalls.Relocation
set_option Elab.async false

theorem Preserves.throw (invariant : Heap → Prop) (exception : ExceptionObject) :
    Preserves invariant (throw exception : Eval α) := by
  intro heap outcome after holds executed
  have same : Except.error exception = outcome ∧ heap = after := by simpa using executed
  exact same.2 ▸ holds

theorem preserves_array (invariant : Heap → Prop) (value : Value) :
    Preserves invariant (Mutable.array value) := by
  unfold Mutable.array
  repeat' first
    | exact Preserves.pure invariant _
    | exact Preserves.throw invariant _
    | exact Preserves.unsupported invariant
    | split
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap

theorem preserves_invalidBinary (invariant : Heap → Prop) (op : BinOp) (value : Value) :
    Preserves invariant (Mutable.invalidBinary op value) := by
  unfold Mutable.invalidBinary
  repeat' first
    | exact Preserves.throw invariant _
    | exact Preserves.unsupported invariant
    | split
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap

theorem preserves_setUnion (left right : Nat) (inPlace : Bool) (invariant : Heap → Prop)
    (stable : if inPlace then UpdateInvariant left invariant else AppendInvariant invariant) :
    Preserves invariant (Mutable.setUnion left right inPlace) := by
  unfold Mutable.setUnion
  apply Preserves.bind _ _ _ (Preserves.get invariant)
  intro heap
  apply Preserves.bind _ _ _ (Preserves.get invariant)
  intro otherHeap
  split
  · cases inPlace with
    | false => exact preserves_allocateSet invariant stable _
    | true => exact preserves_update_return left invariant stable _ _
  · exact Preserves.unsupported invariant

theorem preserves_setDifference (left right : Nat) (inPlace : Bool) (invariant : Heap → Prop)
    (stable : if inPlace then UpdateInvariant left invariant else AppendInvariant invariant) :
    Preserves invariant (Mutable.setDifference left right inPlace) := by
  unfold Mutable.setDifference
  apply Preserves.bind _ _ _ (Preserves.get invariant)
  intro heap
  apply Preserves.bind _ _ _ (Preserves.get invariant)
  intro otherHeap
  split
  · cases inPlace with
    | false => exact preserves_allocateSet invariant stable _
    | true => exact preserves_update_return left invariant stable _ _
  all_goals first | exact Preserves.unsupported invariant | exact Preserves.throw invariant _

theorem preserves_binary_scalar_ref (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (op : BinOp) (left : Constant) (right : Nat) : Preserves invariant (Mutable.binary op (.scalar left) (.ref right)) := by
  cases left <;> cases op <;> dsimp only [Mutable.binary]
  all_goals with_reducible repeat' first
    | exact Preserves.pure invariant _
    | exact Preserves.throw invariant _
    | exact Preserves.unsupported invariant
    | exact preserves_allocate invariant stable _
    | exact preserves_allocateTuple invariant stable _
    | exact preserves_allocateBuffer invariant stable _
    | exact preserves_setUnion _ _ false invariant (by simpa using stable)
    | exact preserves_setDifference _ _ false invariant (by simpa using stable)
    | exact preserves_invalidBinary invariant _ _
    | exact Preserves.error invariant _
    | split
    | apply Preserves.bind _ _ _ (preserves_array invariant _); intro items
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap

theorem preserves_binary_ref_scalar (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (op : BinOp) (left : Nat) (right : Constant) : Preserves invariant (Mutable.binary op (.ref left) (.scalar right)) := by
  cases right <;> cases op <;> dsimp only [Mutable.binary]
  all_goals with_reducible repeat' first
    | exact Preserves.pure invariant _
    | exact Preserves.throw invariant _
    | exact Preserves.unsupported invariant
    | exact preserves_allocate invariant stable _
    | exact preserves_allocateTuple invariant stable _
    | exact preserves_allocateBuffer invariant stable _
    | exact preserves_setUnion _ _ false invariant (by simpa using stable)
    | exact preserves_setDifference _ _ false invariant (by simpa using stable)
    | exact preserves_invalidBinary invariant _ _
    | exact Preserves.error invariant _
    | split
    | apply Preserves.bind _ _ _ (preserves_array invariant _); intro items
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap

theorem preserves_binary_refs (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (op : BinOp) (left right : Nat) : Preserves invariant (Mutable.binary op (.ref left) (.ref right)) := by
  cases op <;> dsimp only [Mutable.binary]
  all_goals with_reducible repeat' first
    | exact Preserves.pure invariant _
    | exact Preserves.throw invariant _
    | exact Preserves.unsupported invariant
    | exact preserves_allocate invariant stable _
    | exact preserves_allocateTuple invariant stable _
    | exact preserves_allocateBuffer invariant stable _
    | exact preserves_setUnion _ _ false invariant (by simpa using stable)
    | exact preserves_setDifference _ _ false invariant (by simpa using stable)
    | exact preserves_invalidBinary invariant _ _
    | exact Preserves.error invariant _
    | split
    | apply Preserves.bind _ _ _ (preserves_array invariant _); intro items
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap

theorem preserves_binary (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (op : BinOp) (left right : Value) : Preserves invariant (Mutable.binary op left right) := by
  cases left with
  | scalar left =>
    cases right with
    | scalar right =>
      rw [binary_scalars]
      exact Preserves.readonly invariant _ (fun heap outcome after executed =>
        (scalarResult_effect heap after (scalarBinary op left right) outcome executed).1)
    | ref address => exact preserves_binary_scalar_ref invariant stable op left address
  | ref address =>
    cases right with
    | scalar right => exact preserves_binary_ref_scalar invariant stable op address right
    | ref other => exact preserves_binary_refs invariant stable op address other

theorem preserves_bufferOperand (invariant : Heap → Prop) (receiver : Option Nat) (value : Value) :
    Preserves invariant (bufferOperand receiver value) :=
  Preserves.readonly invariant _ (fun heap outcome after => bufferOperand_keeps_heap heap after receiver value outcome)

theorem preserves_storeBufferResult (address : Nat) (bytes : List UInt8) (inPlace : Bool) (invariant : Heap → Prop)
    (stable : if inPlace then UpdateInvariant address invariant else AppendInvariant invariant) :
    Preserves invariant (storeBufferResult address bytes inPlace) := by
  cases inPlace with
  | false => exact preserves_allocateBuffer invariant stable bytes
  | true => exact preserves_update_return address invariant stable _ _

theorem preserves_inplaceBinary (address : Nat) (invariant : Heap → Prop)
    (allocate : AppendInvariant invariant) (update : UpdateInvariant address invariant)
    (op : BinOp) (right : Value) : Preserves invariant (Mutable.inplaceBinary op (.ref address) right) := by
  cases op <;> cases right <;> simp only [Mutable.inplaceBinary]
  all_goals first
    | exact preserves_setDifference address _ true invariant (by simpa using update)
    | exact preserves_setUnion address _ true invariant (by simpa using update)
    | exact preserves_binary invariant allocate _ _ _

theorem preserves_inplace_ref (address : Nat) (invariant : Heap → Prop)
    (allocate : AppendInvariant invariant) (update : UpdateInvariant address invariant)
    (op : BinOp) (right : Value) : Preserves invariant (HeapCalls.inplace op (.ref address) right) := by
  intro heap outcome after holds executed
  cases found : heap[address]? with
  | none => simp [HeapCalls.inplace, found, Mutable.unsupported] at executed
  | some object =>
    cases object with
    | list items =>
      by_cases added : op = .add
      · subst op
        rw [inplace_add_list_eval heap address items right found] at executed
        exact Preserves.bind _ _ _ (preserves_sequence invariant right)
          (fun _ => preserves_update_return address invariant update _ _) heap outcome after holds executed
      · by_cases multiplied : op = .mult
        · subst op
          rw [inplace_mult_list_value_eval heap address items right found] at executed
          exact Preserves.bind _ _ _ (preserves_integer invariant right)
            (fun _ => preserves_update_return address invariant update _ _) heap outcome after holds executed
        · rw [inplace_list_fallback heap address items op right found added multiplied] at executed
          exact preserves_binary invariant allocate op (.ref address) right heap outcome after holds executed
    | bytearray bytes =>
      by_cases added : op = .add
      · subst op
        rw [inplace_add_buffer_eval heap address bytes right found] at executed
        exact Preserves.bind _ _ _ (preserves_bufferOperand invariant (some address) right)
          (fun more => preserves_storeBufferResult address (bytes ++ more) true invariant update)
          heap outcome after holds executed
      · by_cases multiplied : op = .mult
        · subst op
          rw [inplace_mult_buffer_eval heap address bytes right found] at executed
          exact Preserves.bind _ _ _ (preserves_integer invariant right)
            (fun count => preserves_storeBufferResult address (List.replicate count.toNat bytes).flatten true invariant update)
            heap outcome after holds executed
        · rw [inplace_buffer_fallback heap address bytes op right found added multiplied] at executed
          exact preserves_binary invariant allocate op (.ref address) right heap outcome after holds executed
    | set items =>
      exact preserves_inplaceBinary address invariant allocate update op right heap outcome after holds
        (by simpa [HeapCalls.inplace, found] using executed)
    | _ =>
      exact preserves_binary invariant allocate op (.ref address) right heap outcome after holds
        (by simpa [HeapCalls.inplace, found] using executed)

theorem preserves_inplace (invariant : Heap → Prop) (allocate : AppendInvariant invariant)
    (op : BinOp) (left right : Value)
    (update : ∀ address, left = .ref address → UpdateInvariant address invariant) :
    Preserves invariant (HeapCalls.inplace op left right) := by
  cases left with
  | scalar scalar => exact preserves_binary invariant allocate op (.scalar scalar) right
  | ref address => exact preserves_inplace_ref address invariant allocate (update address rfl) op right

end FormalSW.PyAst.Heapq
