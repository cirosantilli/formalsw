import lang.py.FormalSW.AcquisitionHeapFrame
import lang.py.FormalSW.PositionalRelocation

/-! Cursor acquisition and reads retain existing cells; sorting completion only allocates. -/
namespace FormalSW.PyAst.Heapq
open Mutable HeapCalls.Relocation
set_option Elab.async false

theorem preserves_permutationRows (invariant : Heap → Prop) (values : List Value) :
    Preserves invariant (HeapCalls.permutationRows values) :=
  Preserves.readonly invariant _ (fun heap outcome after => permutationRows_keeps_heap heap values outcome after)

theorem preserves_combinationRows (invariant : Heap → Prop) (values : List Value) :
    Preserves invariant (HeapCalls.combinationRows values) :=
  Preserves.readonly invariant _ (fun heap outcome after => combinationRows_keeps_heap heap values outcome after)

theorem preserves_zipSources (invariant : Heap → Prop) (values : List Value) :
    Preserves invariant (HeapCalls.zipSources values) :=
  Preserves.readonly invariant _ (fun heap outcome after => zipSources_keeps_heap heap values outcome after)

theorem preserves_zipItem (invariant : Heap → Prop) (sources : List SequenceSource) (position : Nat) :
    Preserves invariant (HeapCalls.zipItem sources position) :=
  Preserves.readonly invariant _ (fun heap outcome after => zipItem_keeps_heap heap sources position outcome after)

theorem preserves_dictionaryItemsNext (invariant : Heap → Prop) (address : Nat)
    (keys : List SequenceSource) (position : Nat) :
    Preserves invariant (HeapCalls.dictionaryItemsNext address keys position) := by
  unfold HeapCalls.dictionaryItemsNext
  with_reducible repeat' first
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | split

theorem preserves_nextSequence (invariant : Heap → Prop) (value : Value) :
    Preserves invariant (HeapCalls.nextSequence value) := by
  unfold HeapCalls.nextSequence
  with_reducible repeat' first
    | exact preserves_sequence invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | split

theorem preserves_sortedFinish (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (reverse : Bool) (keys : List (Value × Value)) :
    Preserves invariant (HeapCalls.sortedFinish reverse keys) := by
  unfold HeapCalls.sortedFinish
  with_reducible repeat' first
    | exact preserves_allocate invariant stable _
    | exact Preserves.throw invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | split

end FormalSW.PyAst.Heapq
