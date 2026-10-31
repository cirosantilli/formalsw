import lang.py.FormalSW.AllocationFrame
import lang.py.FormalSW.ComparisonRelocation

/-! Heap reads preserve arbitrary predicates, including recursive comparisons and failed lookups. -/
namespace FormalSW.PyAst.Heapq
open Mutable Mutable.Relocation HeapCalls.Relocation
set_option Elab.async false

theorem preserves_identity (invariant : Heap → Prop) (left right : Value) :
    Preserves invariant (HeapCalls.identity left right) := by
  unfold HeapCalls.identity
  with_reducible repeat' first
    | exact preserves_scalarResult invariant _
    | exact Preserves.pure invariant _
    | exact Preserves.unsupported invariant
    | split

theorem preserves_unary (invariant : Heap → Prop) (op : UnaryOp) (value : Value) :
    Preserves invariant (HeapCalls.unary op value) := by
  unfold HeapCalls.unary
  with_reducible repeat' first
    | exact preserves_scalarResult invariant _
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | apply Preserves.bind _ _ _ (preserves_truth invariant value); intro truth
    | split

theorem preserves_compareScalars (invariant : Heap → Prop) (op : CmpOp) (left right : Constant) :
    Preserves invariant (HeapCalls.compareScalars op left right) := by
  unfold HeapCalls.compareScalars
  split
  · exact Preserves.pure invariant _
  · exact Preserves.error invariant "TypeError"

theorem preserves_compareDifferent (invariant : Heap → Prop) (op : CmpOp) :
    Preserves invariant (HeapCalls.compareDifferent op) := by
  cases op <;> first | exact Preserves.pure invariant _ | exact Preserves.error invariant "TypeError"

theorem preserves_sequenceCompare (invariant : Heap → Prop) (equality : Bool) (left right : Value) :
    Preserves invariant (HeapCalls.sequenceCompare equality left right) :=
  Preserves.readonly invariant _ (fun heap outcome after => sequenceCompare_keeps_heap heap after equality left right outcome)

theorem preserves_compare (invariant : Heap → Prop) (op : CmpOp) (left right : Value) :
    Preserves invariant (HeapCalls.compare op left right) := by
  unfold HeapCalls.compare
  with_reducible repeat' first
    | exact preserves_compareScalars invariant _ _ _
    | exact preserves_compareDifferent invariant _
    | exact preserves_sequenceCompare invariant _ _ _
    | exact preserves_unary invariant _ _
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind _ _ _ (preserves_array invariant _); rintro ⟨address, items⟩
    | apply Preserves.bind _ _ _ (preserves_sequenceCompare invariant _ _ _); intro answer
    | apply Preserves.bind
    | apply Preserves.mapM
    | intro value
    | split

theorem preserves_sequenceContains (invariant : Heap → Prop) (needle : Value) (items : List Value) :
    Preserves invariant (HeapCalls.sequenceContains needle items) := by
  induction items with
  | nil => exact Preserves.pure invariant false
  | cons item rest ih =>
    unfold HeapCalls.sequenceContains
    split
    · exact Preserves.pure invariant true
    · apply Preserves.bind _ _ _ (preserves_compare invariant .eq item needle)
      intro compared
      apply Preserves.bind _ _ _ (preserves_truth invariant compared)
      intro truth
      split
      · exact Preserves.pure invariant true
      · exact ih

theorem preserves_membershipKey (invariant : Heap → Prop) (needle : Value) :
    Preserves invariant (HeapCalls.membershipKey needle) := by
  unfold HeapCalls.membershipKey
  with_reducible repeat' first
    | exact preserves_hashKey invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | split

theorem preserves_bytesContainsInteger (invariant : Heap → Prop) (bytes : List UInt8) (needle : Int) :
    Preserves invariant (HeapCalls.bytesContainsInteger bytes needle) := by
  unfold HeapCalls.bytesContainsInteger
  split
  · exact Preserves.error invariant "ValueError"
  · exact Preserves.pure invariant _

theorem preserves_bytesContains (invariant : Heap → Prop) (needle : Value) (bytes : List UInt8) :
    Preserves invariant (HeapCalls.bytesContains needle bytes) := by
  unfold HeapCalls.bytesContains
  with_reducible repeat' first
    | exact preserves_bytesContainsInteger invariant _ _
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | split

theorem preserves_membership (invariant : Heap → Prop) (needle container : Value) (negated : Bool) :
    Preserves invariant (HeapCalls.membership needle container negated) := by
  unfold HeapCalls.membership
  with_reducible repeat' first
    | exact preserves_sequenceContains invariant _ _
    | exact preserves_bytesContains invariant _ _
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind _ _ _ (preserves_hashKey invariant _); intro key
    | apply Preserves.bind _ _ _ (preserves_membershipKey invariant _); intro key
    | apply Preserves.bind
    | intro value
    | split

theorem preserves_length (invariant : Heap → Prop) (value : Value) :
    Preserves invariant (Mutable.length value) := by
  unfold Mutable.length
  with_reducible repeat' first
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | split

theorem preserves_dictionaryGet (invariant : Heap → Prop) (address : Nat) (key fallback : Value) :
    Preserves invariant (Mutable.dictionaryGet address key fallback) := by
  unfold Mutable.dictionaryGet
  with_reducible repeat' first
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind _ _ _ (preserves_hashKey invariant _); intro hashed
    | split

theorem preserves_getItem (invariant : Heap → Prop) (base index : Value) :
    Preserves invariant (Mutable.getItem base index) := by
  cases base <;> cases index <;> unfold Mutable.getItem
  all_goals with_reducible repeat' first
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.throw invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind _ _ _ (preserves_index invariant _ _); intro selected
    | apply Preserves.bind _ _ _ (preserves_hashKey invariant _); intro key
    | split
  all_goals first
    | exact Preserves.unsupported invariant
    | exact Preserves.throw invariant _


theorem preserves_readSliceObject (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (address : Nat) (object : Object) (bounds : Py.Builtin.Slice.Slice) :
    Preserves invariant (readSliceObject address object bounds) := by
  unfold readSliceObject
  with_reducible repeat' first
    | exact preserves_allocate invariant stable _
    | exact preserves_allocateTuple invariant stable _
    | exact preserves_allocateBuffer invariant stable _
    | exact Preserves.pure invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (preserves_sliceResult invariant _); intro result
    | split

theorem preserves_getSlice (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (base lower upper stride : Value) : Preserves invariant (Mutable.getSlice base lower upper stride) := by
  cases base with
  | scalar scalar =>
    unfold Mutable.getSlice
    with_reducible repeat' first
      | exact Preserves.pure invariant _
      | exact Preserves.error invariant _
      | exact Preserves.throw invariant _
      | apply Preserves.bind _ _ _ (preserves_sliceBounds invariant lower upper stride); intro bounds
      | dsimp only
      | split
  | ref address =>
    intro heap outcome after holds executed
    cases found : heap[address]? with
    | none => simp [Mutable.getSlice, found, Mutable.unsupported] at executed
    | some object =>
      rw [getSlice_ref heap address object lower upper stride found] at executed
      cases object with
      | list | tuple | bytearray =>
        exact Preserves.bind _ _ _ (preserves_sliceBounds invariant lower upper stride)
          (preserves_readSliceObject invariant stable address _) heap outcome after holds executed
      | dict | keyDict => cases executed
      | _ => exact Preserves.error invariant "TypeError" heap outcome after holds executed

theorem preserves_divmod (invariant : Heap → Prop) (stable : AppendInvariant invariant) (values : List Value) :
    Preserves invariant (Mutable.divmod values) := by
  unfold Mutable.divmod
  with_reducible repeat' first
    | exact preserves_allocateTuple invariant stable _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | split

end FormalSW.PyAst.Heapq
