import lang.py.FormalSW.HeapFrame
import lang.py.FormalSW.MachineSliceInvariant
import lang.py.FormalSW.ListMethodRelocation
import lang.py.FormalSW.BufferArithmeticRelocation
import lang.py.FormalSW.SetOperationsRelocation

/-! Compound mutations retain unrelated cells through conversion, validation and storage. -/
namespace FormalSW.PyAst.Heapq
open Mutable Mutable.Relocation HeapCalls.Relocation
set_option Elab.async false

theorem preserves_sequence (invariant : Heap → Prop) (value : Value) :
    Preserves invariant (Mutable.sequence value) :=
  Preserves.readonly invariant _ (fun heap outcome after => sequence_keeps_heap heap after value outcome)

theorem preserves_byteValues (invariant : Heap → Prop) (value : Value) :
    Preserves invariant (Mutable.byteValues value) :=
  Preserves.readonly invariant _ (fun heap outcome after => byteValues_heap heap after value outcome)

theorem preserves_sliceBounds (invariant : Heap → Prop) (lower upper stride : Value) :
    Preserves invariant (Mutable.sliceBounds lower upper stride) :=
  Preserves.readonly invariant _ (fun heap outcome after => sliceBounds_heap heap after lower upper stride outcome)

theorem preserves_sliceResult {α : Type} (invariant : Heap → Prop) (result : Py.Builtin.Result α) :
    Preserves invariant (sliceResult result) :=
  Preserves.readonly invariant _ (fun heap outcome after => sliceResult_heap heap after result outcome)

theorem preserves_writeSliceObject (address : Nat) (invariant : Heap → Prop)
    (stable : UpdateInvariant address invariant) (object : Object) (replacement : Value)
    (bounds : Py.Builtin.Slice.Slice) : Preserves invariant (writeSliceObject address object replacement bounds) := by
  cases object with
  | list items =>
    apply Preserves.bind _ _ _ (preserves_sequence invariant replacement)
    intro values
    exact Preserves.bind _ _ _ (preserves_sliceResult invariant (Py.Builtin.List.setSlice items bounds values))
      (fun _ => preserves_update_return address invariant stable _ _)
  | bytearray bytes =>
    apply Preserves.bind _ _ _ (preserves_byteValues invariant replacement)
    intro values
    exact Preserves.bind _ _ _ (preserves_sliceResult invariant (Py.Builtin.ByteArray.setSlice bytes bounds values))
      (fun _ => preserves_update_return address invariant stable _ _)
  | _ => exact Preserves.unsupported invariant

theorem preserves_setSlice (address : Nat) (invariant : Heap → Prop)
    (stable : UpdateInvariant address invariant) (lower upper stride replacement : Value) :
    Preserves invariant (Mutable.setSlice (.ref address) lower upper stride replacement) := by
  intro heap outcome after holds executed
  cases found : heap[address]? with
  | none => simp [Mutable.setSlice, found, Mutable.unsupported] at executed
  | some object =>
    rw [setSlice_ref heap address object lower upper stride replacement found] at executed
    cases object with
    | list items | bytearray items =>
      exact Preserves.bind _ _ _ (preserves_sliceBounds invariant lower upper stride)
        (fun bounds => preserves_writeSliceObject address invariant stable _ replacement bounds)
        heap outcome after holds executed
    | dict entries | keyDict entries => cases executed
    | _ => exact Preserves.error invariant "TypeError" heap outcome after holds executed

theorem preserves_clearDictionary (address : Nat) (invariant : Heap → Prop)
    (stable : UpdateInvariant address invariant) : Preserves invariant (HeapCalls.clearDictionary address) := by
  unfold HeapCalls.clearDictionary
  apply Preserves.bind _ _ _ (Preserves.get invariant)
  intro heap
  cases heap[address]? with
  | none => exact Preserves.unsupported invariant
  | some object =>
    cases object with
    | dict entries | keyDict entries => exact preserves_update_return address invariant stable _ _
    | _ => exact Preserves.error invariant "TypeError"

theorem preserves_sortListCore (address : Nat) (invariant : Heap → Prop)
    (stable : UpdateInvariant address invariant) (reverse : Bool) : Preserves invariant (sortListCore address reverse) := by
  intro heap outcome after holds executed
  cases found : heap[address]? with
  | none => simp [sortListCore, found, Mutable.unsupported] at executed
  | some object =>
    cases object with
    | list items =>
      by_cases scalar : scalarValues items
      · cases sorted : HeapSort.sortWithReverse heap reverse items with
        | none => simp [sortListCore, found, scalar, sorted, Mutable.unsupported] at executed
        | some result =>
          cases result with
          | error error => simp [sortListCore, found, scalar, sorted, Mutable.unsupported] at executed
          | ok values =>
            simp [sortListCore, found, scalar, sorted, Except.map] at executed
            exact executed.2 ▸ stable heap (.list values) holds
      · simp [sortListCore, found, scalar, Mutable.unsupported] at executed
    | _ => simp [sortListCore, found, Mutable.unsupported] at executed

theorem preserves_truth (invariant : Heap → Prop) (value : Value) : Preserves invariant (Mutable.truth value) := by
  apply Preserves.readonly
  intro heap outcome after executed
  cases value with
  | scalar scalar => simp [Mutable.truth] at executed; exact executed.2.symm
  | ref address =>
    cases found : heap[address]? with
    | none => simp [Mutable.truth, found, Mutable.unsupported] at executed
    | some object =>
      cases object <;> simp [Mutable.truth, found] at executed
      all_goals exact executed.2.symm

theorem preserves_sortDirection (invariant : Heap → Prop) (value : Value) :
    Preserves invariant (sortDirection value) := by
  apply Preserves.readonly
  intro heap outcome after executed
  cases value with
  | scalar scalar =>
    exact (preserves_truth (fun h => h = heap) (.scalar scalar)) heap outcome after rfl executed
  | ref address =>
    cases found : heap[address]? with
    | none =>
      apply (preserves_truth (fun h => h = heap) (.ref address)) heap outcome after rfl
      simpa [sortDirection, found] using executed
    | some object =>
      cases object with
      | «instance» _ _ _ | dataInstance _ _ _ _ _ => simp [sortDirection, found, Mutable.unsupported] at executed
      | _ =>
        apply (preserves_truth (fun h => h = heap) (.ref address)) heap outcome after rfl
        simpa [sortDirection, found] using executed

theorem preserves_sort (address : Nat) (invariant : Heap → Prop)
    (stable : UpdateInvariant address invariant) : Preserves invariant (HeapCalls.primitive (.sort address) []) := by
  rw [primitive_sort_core]
  exact preserves_sortListCore address invariant stable false

theorem preserves_sortReverse (address : Nat) (invariant : Heap → Prop)
    (stable : UpdateInvariant address invariant) (reverse : Value) :
    Preserves invariant (HeapCalls.primitive (.sortReverse address) [reverse]) := by
  rw [primitive_sortReverse_core]
  exact Preserves.bind _ _ _ (preserves_sortDirection invariant reverse)
    (preserves_sortListCore address invariant stable)

end FormalSW.PyAst.Heapq
