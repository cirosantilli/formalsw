import lang.py.FormalSW.HeapqPreservation
import lang.py.FormalSW.SequenceMethodRelocation

/-! Unrelated heap cells survive allocation and receiver-local mutations, including errors. -/
namespace FormalSW.PyAst.Heapq
open Mutable
set_option Elab.async false

theorem Preserves.unsupported (invariant : Heap → Prop) :
    Preserves invariant (Mutable.unsupported : Eval α) := by
  intro heap outcome after _ executed
  simp [Mutable.unsupported] at executed

theorem Preserves.get (invariant : Heap → Prop) : Preserves invariant (get : Eval Heap) := by
  intro heap outcome after holds executed
  simp only [Mutable.eval_get, Option.some.injEq, Prod.mk.injEq] at executed
  exact executed.2 ▸ holds

theorem Preserves.modify (invariant : Heap → Prop) (update : Heap → Heap)
    (stable : ∀ heap, invariant heap → invariant (update heap)) :
    Preserves invariant (modify update : Eval PUnit) := by
  intro heap outcome after holds executed
  simp only [Mutable.eval_modify, Option.some.injEq, Prod.mk.injEq] at executed
  exact executed.2 ▸ stable heap holds

theorem Preserves.readonly (invariant : Heap → Prop) (action : Eval α)
    (same : ∀ heap outcome after, action heap = some (outcome, after) → after = heap) :
    Preserves invariant action := by
  intro heap outcome after holds executed
  exact same heap outcome after executed ▸ holds

theorem Preserves.total_readonly (invariant : Heap → Prop) (action : Eval α)
    (same : ∀ heap, ∃ outcome, action heap = some (outcome, heap)) : Preserves invariant action := by
  apply Preserves.readonly invariant action
  intro heap outcome after executed
  obtain ⟨result, finished⟩ := same heap
  rw [finished] at executed
  exact (congrArg Prod.snd (Option.some.inj executed)).symm

/-- Updating the designated receiver retains the predicate regardless of its new contents. -/
def UpdateInvariant (address : Nat) (invariant : Heap → Prop) : Prop :=
  ∀ heap object, invariant heap → invariant (heap.set address object)

theorem preserves_update_return (address : Nat) (invariant : Heap → Prop)
    (stable : UpdateInvariant address invariant) (object : Object) (value : α) :
    Preserves invariant (do modify fun heap => heap.set address object; pure value : Eval α) :=
  Preserves.bind _ _ _ (Preserves.modify invariant _ (fun heap => stable heap object))
    (fun _ => Preserves.pure invariant value)

theorem preserves_integer (invariant : Heap → Prop) (value : Value) :
    Preserves invariant (Mutable.integer value) :=
  Preserves.total_readonly invariant _ (fun heap => Mutable.Relocation.integer_total heap value)

theorem preserves_byte (invariant : Heap → Prop) (value : Value) :
    Preserves invariant (Mutable.byte value) :=
  Preserves.total_readonly invariant _ (fun heap => Mutable.Relocation.byte_total heap value)

theorem preserves_index {α : Type} (invariant : Heap → Prop) (values : List α) (index : Value) :
    Preserves invariant (Mutable.index values index) := by
  apply Preserves.total_readonly
  intro heap
  obtain ⟨outcome, executed, _⟩ := Mutable.Relocation.index_total values index heap
  exact ⟨outcome, executed⟩

theorem preserves_hashKey (invariant : Heap → Prop) (value : Value) :
    Preserves invariant (Mutable.hashKey value) := by
  apply Preserves.readonly
  intro heap outcome after executed
  cases found : Mutable.keyOf heap value with
  | none => simp [Mutable.hashKey, found] at executed
  | some result =>
    cases result <;> simp [Mutable.hashKey, found] at executed
    all_goals exact executed.2.symm

theorem preserves_appendItem (address : Nat) (invariant : Heap → Prop)
    (stable : UpdateInvariant address invariant) (value : Value) :
    Preserves invariant (Mutable.appendItem address value) := by
  unfold Mutable.appendItem
  apply Preserves.bind _ _ _ (Preserves.get invariant)
  intro heap
  cases heap[address]? with
  | none => exact Preserves.unsupported invariant
  | some object =>
    cases object with
    | list values => exact preserves_update_return address invariant stable _ _
    | bytearray bytes =>
      exact Preserves.bind _ _ _ (preserves_byte invariant value)
        (fun _ => preserves_update_return address invariant stable _ _)
    | _ => exact Preserves.error invariant "AttributeError"

theorem preserves_setItem (address : Nat) (invariant : Heap → Prop)
    (stable : UpdateInvariant address invariant) (index value : Value) :
    Preserves invariant (Mutable.setItem (.ref address) index value) := by
  simp only [Mutable.setItem]
  apply Preserves.bind _ _ _ (Preserves.get invariant)
  intro heap
  cases heap[address]? with
  | none => exact Preserves.unsupported invariant
  | some object =>
    cases object with
    | list values =>
      exact Preserves.bind _ _ _ (preserves_index invariant values index)
        (fun _ => preserves_update_return address invariant stable _ _)
    | bytearray bytes =>
      apply Preserves.bind _ _ _ (preserves_integer invariant index)
      intro number
      apply Preserves.bind _ _ _ (preserves_byte invariant value)
      intro byte
      exact Preserves.bind _ _ _ (preserves_index invariant bytes (.scalar (.int number)))
        (fun _ => preserves_update_return address invariant stable _ _)
    | dict entries =>
      cases index with
      | scalar key => exact preserves_update_return address invariant stable _ _
      | ref keyAddress =>
        exact Preserves.bind _ _ _ (preserves_hashKey invariant (.ref keyAddress))
          (fun _ => preserves_update_return address invariant stable _ _)
    | keyDict entries =>
      exact Preserves.bind _ _ _ (preserves_hashKey invariant index)
        (fun _ => preserves_update_return address invariant stable _ _)
    | _ => exact Preserves.error invariant "TypeError"

/-- Allocation preserves any predicate stable under appending one object. -/
def AppendInvariant (invariant : Heap → Prop) : Prop :=
  ∀ heap object, invariant heap → invariant (heap ++ [object])

theorem preserves_allocate (invariant : Heap → Prop) (stable : AppendInvariant invariant) (values : List Value) :
    Preserves invariant (Mutable.allocate values) := by
  intro heap outcome after holds executed
  simp [Mutable.allocate, Except.map] at executed
  exact executed.2 ▸ stable heap (.list values) holds

theorem preserves_allocateBuffer (invariant : Heap → Prop) (stable : AppendInvariant invariant) (bytes : List UInt8) :
    Preserves invariant (Mutable.allocateBuffer bytes) := by
  intro heap outcome after holds executed
  simp [Mutable.allocateBuffer, Except.map] at executed
  exact executed.2 ▸ stable heap (.bytearray bytes) holds

theorem preserves_allocateSet (invariant : Heap → Prop) (stable : AppendInvariant invariant) (values : List Constant) :
    Preserves invariant (Mutable.allocateSet values) := by
  intro heap outcome after holds executed
  simp [Mutable.allocateSet, Except.map] at executed
  exact executed.2 ▸ stable heap (.set values) holds

theorem preserves_allocateDict (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (entries : List (Constant × Value)) : Preserves invariant (Mutable.allocateDict entries) := by
  intro heap outcome after holds executed
  simp [Mutable.allocateDict, Except.map] at executed
  exact executed.2 ▸ stable heap (.dict entries) holds

theorem preserves_allocateTuple (invariant : Heap → Prop) (stable : AppendInvariant invariant) (values : List Value) :
    Preserves invariant (Mutable.allocateTuple values) := by
  intro heap outcome after holds executed
  by_cases empty : values.isEmpty
  · cases interned : heap.findIdx? (fun object => decide (object = .tuple [])) with
    | none =>
      simp [Mutable.allocateTuple, empty, interned, Except.map] at executed
      exact executed.2 ▸ stable heap (.tuple []) holds
    | some address =>
      simp [Mutable.allocateTuple, empty, interned] at executed
      exact executed.2 ▸ holds
  · simp [Mutable.allocateTuple, empty, Except.map] at executed
    exact executed.2 ▸ stable heap (.tuple values) holds

theorem preserves_instanceData (invariant : Heap → Prop) (receiver : Value) :
    Preserves invariant (Mutable.instanceData receiver) := by
  apply Preserves.readonly
  intro heap outcome after executed
  cases receiver with
  | scalar scalar => simp [Mutable.instanceData, Mutable.error] at executed; exact executed.2.symm
  | ref address =>
    cases found : heap[address]? with
    | none => simp [Mutable.instanceData, found, Mutable.unsupported] at executed
    | some object =>
      cases object <;> simp [Mutable.instanceData, found, Mutable.error] at executed
      all_goals exact executed.2.symm

theorem preserves_writeField (address : Nat) (invariant : Heap → Prop)
    (stable : UpdateInvariant address invariant) (name : String) (value : Value) :
    Preserves invariant (Mutable.writeField (.ref address) name value) := by
  simp only [Mutable.writeField]
  split
  · exact Preserves.unsupported invariant
  · apply Preserves.bind _ _ _ (preserves_instanceData invariant (.ref address))
    rintro ⟨origin, className, fields⟩
    apply Preserves.bind _ _ _ (Preserves.get invariant)
    intro heap
    cases heap[address]? with
    | none => exact preserves_update_return address invariant stable _ _
    | some object =>
      cases object <;> try exact preserves_update_return address invariant stable _ _
      case dataInstance oldOrigin oldClass frozen declared oldFields =>
        cases frozen with
        | false => exact preserves_update_return address invariant stable _ _
        | true => exact Preserves.error invariant "FrozenInstanceError"

theorem preserves_popItem_integer (address : Nat) (invariant : Heap → Prop)
    (stable : UpdateInvariant address invariant) (index : Int) :
    Preserves invariant (Mutable.popItem address (.scalar (.int index))) := by
  intro heap outcome after holds executed
  cases found : heap[address]? with
  | none => simp [Mutable.popItem, Mutable.integer, found, Mutable.unsupported] at executed
  | some object =>
    cases object with
    | list values =>
      rw [Mutable.Relocation.popItem_list_selection heap address values index found] at executed
      cases selected : Mutable.Relocation.popSelection values index with
      | none => simp [selected] at executed; exact executed.2 ▸ holds
      | some pair =>
        rcases pair with ⟨value, remaining⟩
        simp [selected] at executed
        exact executed.2 ▸ stable heap (.list remaining) holds
    | bytearray bytes =>
      rw [Mutable.Relocation.popItem_buffer_selection heap address bytes index found] at executed
      cases selected : Mutable.Relocation.popSelection bytes index with
      | none => simp [selected] at executed; exact executed.2 ▸ holds
      | some pair =>
        rcases pair with ⟨value, remaining⟩
        simp [selected] at executed
        exact executed.2 ▸ stable heap (.bytearray remaining) holds
    | _ =>
      simp [Mutable.popItem, Mutable.integer, found, Mutable.error] at executed
      exact executed.2 ▸ holds

theorem preserves_popItem (address : Nat) (invariant : Heap → Prop)
    (stable : UpdateInvariant address invariant) (index : Value) :
    Preserves invariant (Mutable.popItem address index) := by
  have expanded := funext (fun heap => Mutable.Relocation.popItem_index heap address index)
  rw [expanded]
  exact Preserves.bind _ _ _
    (Preserves.readonly invariant _ (fun heap outcome after => Mutable.Relocation.popIndex_heap heap after index outcome))
    (fun number => preserves_popItem_integer address invariant stable number)

theorem preserves_addItem (address : Nat) (invariant : Heap → Prop)
    (stable : UpdateInvariant address invariant) (value : Value) :
    Preserves invariant (Mutable.addItem address value) := by
  unfold Mutable.addItem
  apply Preserves.bind _ _ _ (Preserves.get invariant)
  intro heap
  cases heap[address]? with
  | none => exact Preserves.unsupported invariant
  | some object =>
    cases object with
    | set values =>
      cases value with
      | scalar item => exact preserves_update_return address invariant stable _ _
      | ref other =>
        exact Preserves.bind _ _ _ (preserves_hashKey invariant (.ref other))
          (fun _ => preserves_update_return address invariant stable _ _)
    | keySet entries =>
      exact Preserves.bind _ _ _ (preserves_hashKey invariant value)
        (fun _ => preserves_update_return address invariant stable _ _)
    | _ => exact Preserves.error invariant "AttributeError"

theorem preserves_dictionarySetDefault (address : Nat) (invariant : Heap → Prop)
    (stable : UpdateInvariant address invariant) (key defaultValue : Value) :
    Preserves invariant (Mutable.dictionarySetDefault address key defaultValue) := by
  unfold Mutable.dictionarySetDefault
  apply Preserves.bind _ _ _ (Preserves.get invariant)
  intro heap
  cases heap[address]? with
  | none => exact Preserves.unsupported invariant
  | some object =>
    cases object with
    | dict entries =>
      cases key with
      | scalar key =>
        dsimp only
        cases ScalarDict.lookup entries key with
        | none => exact preserves_update_return address invariant stable _ _
        | some value => exact Preserves.pure invariant value
      | ref keyAddress =>
        apply Preserves.bind _ _ _ (preserves_hashKey invariant (.ref keyAddress))
        intro hashed
        dsimp only
        cases HashDict.lookup (Mutable.promoteDictionary entries) hashed with
        | none => exact preserves_update_return address invariant stable _ _
        | some value => exact Preserves.pure invariant value
    | keyDict entries =>
      apply Preserves.bind _ _ _ (preserves_hashKey invariant key)
      intro hashed
      dsimp only
      cases HashDict.lookup entries hashed with
      | none => exact preserves_update_return address invariant stable _ _
      | some value => exact Preserves.pure invariant value
    | _ => exact Preserves.error invariant "TypeError"

theorem UpdateInvariant.swaps (address : Nat) (invariant : Heap → Prop)
    (stable : UpdateInvariant address invariant) : SwapInvariant address invariant :=
  fun heap _ _ _ _ _ holds _ => stable heap _ holds

/-- A checked receiver is the original address, so later mutations remain local. -/
theorem preserves_receiver_bind (address : Nat) (invariant : Heap → Prop) (next : Nat → Eval α)
    (following : Preserves invariant (next address)) :
    Preserves invariant (receiver (.ref address) >>= next) := by
  intro heap outcome after holds executed
  cases found : heap[address]? with
  | none => simp [receiver, items, found, Mutable.unsupported] at executed
  | some object =>
    cases object with
    | list values =>
      apply following heap outcome after holds
      simpa [receiver, items, found] using executed
    | _ =>
      simp [receiver, items, found, Mutable.error, Except.map] at executed
      exact executed.2 ▸ holds

theorem preserves_heappush (address : Nat) (invariant : Heap → Prop)
    (stable : UpdateInvariant address invariant) (value : Value) :
    Preserves invariant (heappush [.ref address, value]) := by
  apply preserves_receiver_bind address invariant
  apply Preserves.bind _ _ _ (preserves_items invariant address)
  intro values
  apply Preserves.bind _ _ _ (preserves_appendItem address invariant stable value)
  intro _
  exact Preserves.bind _ _ _ (preserves_siftDown address 0 values.length invariant (stable.swaps address invariant))
    (fun _ => Preserves.pure invariant (.scalar .none : Value))

theorem preserves_heappop (address : Nat) (invariant : Heap → Prop)
    (stable : UpdateInvariant address invariant) : Preserves invariant (heappop [.ref address]) := by
  apply preserves_receiver_bind address invariant
  apply Preserves.bind _ _ _ (preserves_popItem address invariant stable (.scalar (.int (-1))))
  intro last
  apply Preserves.bind _ _ _ (preserves_items invariant address)
  intro values
  cases values with
  | nil => exact Preserves.pure invariant last
  | cons first rest =>
    apply Preserves.bind _ _ _ (Preserves.modify invariant _ (fun heap => stable heap (.list (last :: rest))))
    intro _
    exact Preserves.bind _ _ _ (preserves_siftUp address 0 invariant (stable.swaps address invariant))
      (fun _ => Preserves.pure invariant first)

end FormalSW.PyAst.Heapq

namespace FormalSW.PyAst.Mutable.Relocation
open Heapq

/-- The exact object in a private cell, including every stored reference, is unchanged. -/
def SavedCell (address : Nat) (object : Object) (heap : Heap) : Prop := heap[address]? = some object

theorem SavedCell.update (address receiver : Nat) (object : Object) (separate : receiver ≠ address) :
    UpdateInvariant receiver (SavedCell address object) := by
  intro heap replacement saved
  simpa [SavedCell, separate] using saved

theorem SavedCell.append (address : Nat) (object : Object) (heap extra : Heap)
    (saved : SavedCell address object heap) : SavedCell address object (heap ++ extra) := by
  have inside := (List.getElem?_eq_some_iff.mp saved).1
  simpa only [SavedCell, List.getElem?_append_left inside] using saved

theorem appendItem_preserves_cell (address receiver : Nat) (object : Object) (value : Value)
    (separate : receiver ≠ address) :
    Heapq.Preserves (SavedCell address object) (Mutable.appendItem receiver value) :=
  preserves_appendItem receiver _ (SavedCell.update address receiver object separate) value

theorem setItem_preserves_cell (address receiver : Nat) (object : Object) (index value : Value)
    (separate : receiver ≠ address) :
    Heapq.Preserves (SavedCell address object) (Mutable.setItem (.ref receiver) index value) :=
  preserves_setItem receiver _ (SavedCell.update address receiver object separate) index value

theorem SavedCell.allocates (address : Nat) (object : Object) : AppendInvariant (SavedCell address object) :=
  fun heap extra saved => saved.append address object heap [extra]

theorem writeField_preserves_cell (address receiver : Nat) (object : Object) (name : String) (value : Value)
    (separate : receiver ≠ address) :
    Heapq.Preserves (SavedCell address object) (Mutable.writeField (.ref receiver) name value) :=
  preserves_writeField receiver _ (SavedCell.update address receiver object separate) name value

theorem popItem_preserves_cell (address receiver : Nat) (object : Object) (index : Value)
    (separate : receiver ≠ address) :
    Heapq.Preserves (SavedCell address object) (Mutable.popItem receiver index) :=
  preserves_popItem receiver _ (SavedCell.update address receiver object separate) index

end FormalSW.PyAst.Mutable.Relocation
