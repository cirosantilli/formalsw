import lang.py.FormalSW.ReadHeapFrame
import lang.py.FormalSW.MachineAttributes

/-! Attribute binding and sequence acquisition preserve arbitrary heap predicates. -/
namespace FormalSW.PyAst.Heapq
open Mutable
set_option Elab.async false

theorem preserves_instanceClass (invariant : Heap → Prop) (module : Module) (origin name : String) :
    Preserves invariant (HeapCalls.instanceClass module origin name) := by
  unfold HeapCalls.instanceClass
  with_reducible repeat' first
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind
    | intro value
    | split

theorem preserves_getAttribute (invariant : Heap → Prop) (module : Module) (receiver : Value) (name : String) :
    Preserves invariant (HeapCalls.getAttribute module receiver name) := by
  unfold HeapCalls.getAttribute
  with_reducible repeat' first
    | exact preserves_instanceClass invariant _ _ _
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind _ _ _ (preserves_instanceClass invariant _ _ _); intro value
    | apply Preserves.bind
    | intro value
    | split

theorem preserves_bindMethod (invariant : Heap → Prop) (module : Module) (receiver : Value) (name : String) :
    Preserves invariant (HeapCalls.bindMethod module receiver name) := by
  apply Preserves.readonly
  intro heap outcome after executed
  by_cases inside : receiver.edge.Within heap.length
  · exact HeapCalls.Relocation.bindMethod_keeps_heap module receiver name heap after outcome inside executed
  · cases receiver with
    | scalar scalar => simp [Value.edge, Graph.Edge.Within] at inside
    | ref address =>
      have missing : heap[address]? = none := List.getElem?_eq_none (by simpa [Value.edge, Graph.Edge.Within] using inside)
      by_cases reverse : name = "$formalsw.sort.reverse"
      · simp [HeapCalls.bindMethod, reverse, eval_bind, missing, unsupported] at executed
      · simp [HeapCalls.bindMethod, reverse, eval_bind, missing, unsupported] at executed

theorem preserves_starItems (invariant : Heap → Prop) (value : Value) :
    Preserves invariant (HeapCalls.starItems value) := by
  unfold HeapCalls.starItems
  with_reducible repeat' first
    | exact preserves_sequence invariant _
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind _ _ _ (preserves_sequence invariant _); intro value
    | apply Preserves.bind
    | intro value
    | split

theorem preserves_sortedItems (invariant : Heap → Prop) (source : Value) :
    Preserves invariant (HeapCalls.sortedItems source) := by
  unfold HeapCalls.sortedItems
  with_reducible repeat' first
    | exact preserves_sequence invariant _
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind _ _ _ (preserves_sequence invariant _); intro value
    | apply Preserves.bind
    | intro value
    | split

theorem preserves_sortedStart (invariant : Heap → Prop) (source reverse : Value) :
    Preserves invariant (HeapCalls.sortedStart source reverse) := by
  unfold HeapCalls.sortedStart
  with_reducible repeat' first
    | exact preserves_sortedItems invariant _
    | exact preserves_truth invariant _
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind _ _ _ (preserves_sortedItems invariant _); intro value
    | apply Preserves.bind _ _ _ (preserves_truth invariant _); intro value
    | apply Preserves.bind
    | intro value
    | split

theorem preserves_extremumItem (invariant : Heap → Prop) (source : Value) (position : Nat) :
    Preserves invariant (HeapCalls.extremumItem source position) := by
  unfold HeapCalls.extremumItem
  with_reducible repeat' first
    | exact preserves_sequence invariant _
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind _ _ _ (preserves_sequence invariant _); intro value
    | apply Preserves.bind
    | intro value
    | split

theorem preserves_extremumChoose (invariant : Heap → Prop) (cursor : HeapCalls.SequenceExtremum) (candidate score : Value) (best : Option (Value × Value)) :
    Preserves invariant (HeapCalls.SequenceExtremum.choose cursor candidate score best) := by
  unfold HeapCalls.SequenceExtremum.choose
  with_reducible repeat' first
    | exact preserves_compare invariant _ _ _
    | exact preserves_truth invariant _
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind _ _ _ (preserves_compare invariant _ _ _); intro value
    | apply Preserves.bind _ _ _ (preserves_truth invariant _); intro value
    | apply Preserves.bind
    | intro value
    | split

theorem preserves_sumInitial (invariant : Heap → Prop) (value : Value) :
    Preserves invariant (HeapCalls.sumInitial value) := by
  unfold HeapCalls.sumInitial
  with_reducible repeat' first
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind
    | intro value
    | split

theorem preserves_enumerateStart (invariant : Heap → Prop) (value : Value) :
    Preserves invariant (HeapCalls.enumerateStart value) := by
  unfold HeapCalls.enumerateStart
  with_reducible repeat' first
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind
    | intro value
    | split

theorem preserves_addReceiver (invariant : Heap → Prop) (value : Value) :
    Preserves invariant (Mutable.addReceiver value) := by
  unfold Mutable.addReceiver
  with_reducible repeat' first
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind
    | intro value
    | split

theorem preserves_appendReceiver (invariant : Heap → Prop) (value : Value) :
    Preserves invariant (Mutable.appendReceiver value) := by
  unfold Mutable.appendReceiver
  with_reducible repeat' first
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind
    | intro value
    | split

theorem preserves_reversibleSequence (invariant : Heap → Prop) (value : Value) :
    Preserves invariant (Mutable.reversibleSequence value) := by
  unfold Mutable.reversibleSequence
  with_reducible repeat' first
    | exact preserves_sequence invariant _
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind _ _ _ (preserves_sequence invariant _); intro value
    | apply Preserves.bind
    | intro value
    | split

end FormalSW.PyAst.Heapq
