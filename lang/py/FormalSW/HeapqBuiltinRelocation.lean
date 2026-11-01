import lang.py.FormalSW.HeapqRelocation
import lang.py.FormalSW.SequenceMethodRelocation
import lang.py.FormalSW.HeapqContents

/-! Heap builtins retain their initial append, removal and root replacement on sift errors. -/
namespace FormalSW.PyAst.Heapq.Relocation
open Mutable.Relocation
set_option Elab.async false

variable {logical physical : Heap} {rename : Nat → Nat}

theorem items_success (heap after : Heap) (address : Nat) (values : List Value)
    (read : items address heap = some (.ok values, after)) : heap[address]? = some (.list values) := by
  cases found : heap[address]? with
  | none => simp [items, found, Mutable.unsupported] at read
  | some object =>
    cases object <;> simp [items, found, Mutable.error] at read
    case list old => simp [read.1]

theorem receiver_relocates (layout : RuntimeLayout logical physical rename)
    (value : Value) (inside : value.edge.Within logical.length) :
    receiver (relocateValue rename value) physical =
      (receiver value logical).map (fun pair => (pair.1.map rename, physical)) := by
  cases value with
  | scalar scalar => rfl
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    cases object : logical[address] <;>
      simp [receiver, items, relocateValue, found, moved, object, relocateObject, Mutable.error, Except.map]

theorem receiver_bounded (heap after : Heap) (value : Value) (address : Nat)
    (inside : value.edge.Within heap.length) (read : receiver value heap = some (.ok address, after)) :
    address < heap.length := by
  cases value with
  | scalar scalar => simp [receiver, Mutable.error] at read
  | ref old =>
    cases found : heap[old]? with
    | none => simp [receiver, items, found, Mutable.unsupported] at read
    | some object =>
      cases object <;> simp [receiver, items, found, Mutable.error] at read
      exact read.1 ▸ inside

theorem receiver_bind_relocates {α β : Type} (layout : ExecutionLayout logical physical rename)
    (value : Value) (inside : value.edge.Within logical.length) (convert : α → β)
    (next : Nat → Eval α) (otherNext : Nat → Eval β)
    (following : ∀ address, address < logical.length →
      MutationRelocates logical physical rename convert (next address) (otherNext (rename address))) :
    MutationRelocates logical physical rename convert (receiver value >>= next)
      (receiver (relocateValue rename value) >>= otherNext) := by
  apply MutationRelocates.readonly_bind layout rename convert _ _ _ _ (receiver_relocates layout.runtime value inside)
    (fun outcome after read => preserves_receiver (fun after => after = logical) value logical outcome after rfl read)
  intro address read
  exact following address (receiver_bounded logical logical value address inside read)

theorem items_bind_relocates {α β : Type} (layout : ExecutionLayout logical physical rename)
    (address : Nat) (inside : address < logical.length) (convert : α → β)
    (next : List Value → Eval α) (otherNext : List Value → Eval β)
    (following : ∀ values, logical[address]? = some (.list values) →
      MutationRelocates logical physical rename convert (next values) (otherNext (values.map (relocateValue rename)))) :
    MutationRelocates logical physical rename convert (items address >>= next) (items (rename address) >>= otherNext) := by
  apply MutationRelocates.readonly_bind layout (List.map (relocateValue rename)) convert _ _ _ _
    (items_relocates layout.runtime address inside)
    (fun outcome after read => preserves_items (fun after => after = logical) address logical outcome after rfl read)
  intro values read
  exact following values (items_success logical logical address values read)

theorem append_relocates (layout : ExecutionLayout logical physical rename) (address : Nat) (value : Value)
    (inside : address < logical.length) (valueInside : value.edge.Within logical.length) :
    MutationRelocates logical physical rename (relocateValue rename) (Mutable.appendItem address value)
      (Mutable.appendItem (rename address) (relocateValue rename value)) := by
  obtain ⟨outcome, after, other, first, second, retained, left, right, _⟩ :=
    layout.appendItem address value inside valueInside
  simp only [MutationRelocates, first]
  exact ⟨other, second, retained, left, right⟩

theorem pop_last_relocates (layout : ExecutionLayout logical physical rename) (address : Nat)
    (inside : address < logical.length) :
    MutationRelocates logical physical rename (relocateValue rename)
      (Mutable.popItem address (.scalar (.int (-1)))) (Mutable.popItem (rename address) (.scalar (.int (-1)))) := by
  obtain ⟨outcome, after, other, first, second, retained, left, right, _⟩ := layout.popItem_integer address (-1) inside
  simp only [MutationRelocates, first]
  exact ⟨other, second, retained, left, right⟩

theorem pop_last_bounded (layout : ExecutionLayout logical physical rename) (address : Nat)
    (inside : address < logical.length) (value : Value) (after : Heap)
    (popped : Mutable.popItem address (.scalar (.int (-1))) logical = some (.ok value, after)) :
    value.edge.Within after.length := by
  obtain ⟨outcome, middle, other, first, _, _, _, _, bounded⟩ := layout.popItem_integer address (-1) inside
  rw [popped] at first
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj first)
  exact bounded value rfl

theorem replace_list_relocates (layout : ExecutionLayout logical physical rename)
    (address : Nat) (old updated : List Value) (found : logical[address]? = some (.list old))
    (inside : ∀ value ∈ updated, value.edge.Within logical.length) :
    MutationRelocates logical physical rename id
      (modify fun heap => heap.set address (.list updated))
      (modify fun heap => heap.set (rename address) (.list (updated.map (relocateValue rename)))) := by
  exact ⟨_, rfl, layout.set_list address old updated found inside, by simp, by simp⟩

theorem heapify_relocates (layout : ExecutionLayout logical physical rename)
    (values : List Value) (inside : ∀ value ∈ values, value.edge.Within logical.length) :
    MutationRelocates logical physical rename (relocateValue rename) (heapify values)
      (heapify (values.map (relocateValue rename))) := by
  rcases values with _ | ⟨value, _ | ⟨extra, rest⟩⟩
  · exact MutationRelocates.error layout _ "TypeError"
  · apply receiver_bind_relocates layout value (inside value (by simp))
    intro address valid
    apply items_bind_relocates layout address valid
    intro values _
    simp only [List.length_map]
    apply MutationRelocates.bind id (relocateValue rename) _ _ _ _
      (siftAll_relocates layout address (heapifyOrder values.length) valid)
    intro _ middle other _ retained _ _
    exact MutationRelocates.pure retained (relocateValue rename) (.scalar .none)
  · exact MutationRelocates.error layout _ "TypeError"

theorem heappush_relocates (layout : ExecutionLayout logical physical rename)
    (values : List Value) (inside : ∀ value ∈ values, value.edge.Within logical.length) :
    MutationRelocates logical physical rename (relocateValue rename) (heappush values)
      (heappush (values.map (relocateValue rename))) := by
  rcases values with _ | ⟨value, _ | ⟨item, _ | ⟨extra, rest⟩⟩⟩
  · exact MutationRelocates.error layout _ "TypeError"
  · exact MutationRelocates.error layout _ "TypeError"
  · apply receiver_bind_relocates layout value (inside value (by simp))
    intro address valid
    apply items_bind_relocates layout address valid
    intro values _
    simp only [List.length_map]
    apply MutationRelocates.bind (relocateValue rename) (relocateValue rename) _ _ _ _
      (append_relocates layout address item valid (inside item (by simp)))
    intro _ middle other _ retained length _
    apply MutationRelocates.bind id (relocateValue rename) _ _ _ _
      (siftDown_relocates retained address 0 values.length (by omega))
    intro _ final otherFinal _ finalLayout _ _
    exact MutationRelocates.pure finalLayout (relocateValue rename) (.scalar .none)
  · exact MutationRelocates.error layout _ "TypeError"

theorem heappop_relocates (layout : ExecutionLayout logical physical rename)
    (values : List Value) (inside : ∀ value ∈ values, value.edge.Within logical.length) :
    MutationRelocates logical physical rename (relocateValue rename) (heappop values)
      (heappop (values.map (relocateValue rename))) := by
  rcases values with _ | ⟨value, _ | ⟨extra, rest⟩⟩
  · exact MutationRelocates.error layout _ "TypeError"
  · apply receiver_bind_relocates layout value (inside value (by simp))
    intro address valid
    apply MutationRelocates.bind (relocateValue rename) (relocateValue rename) _ _ _ _
      (pop_last_relocates layout address valid)
    intro last middle other popped retained length _
    have lastInside := pop_last_bounded layout address valid last middle popped
    apply items_bind_relocates retained address (by omega)
    intro values found
    cases values with
    | nil => exact MutationRelocates.pure retained (relocateValue rename) last
    | cons root rest =>
      have bounded := retained.closed _ (List.mem_of_getElem? found)
      have updated : ∀ value ∈ last :: rest, value.edge.Within middle.length := by
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact lastInside
        · exact bounded value (List.mem_cons_of_mem _ member)
      apply MutationRelocates.bind id (relocateValue rename) _ _ _ _
        (replace_list_relocates retained address (root :: rest) (last :: rest) found updated)
      intro _ replaced otherReplaced _ replacement replacedLength _
      apply MutationRelocates.bind id (relocateValue rename) _ _ _ _
        (siftUp_relocates replacement address 0 (by omega))
      intro _ final otherFinal _ finalLayout _ _
      exact MutationRelocates.pure finalLayout (relocateValue rename) root
  · exact MutationRelocates.error layout _ "TypeError"

section ReturnBounds
attribute [local simp] Except.map

theorem constant_map_returns {α : Type} (action : Eval α) (heap after : Heap) (value returned : Value)
    (executed : ((fun _ => value) <$> action) heap = some (.ok returned, after)) : returned = value := by
  rw [Mutable.eval_map] at executed
  cases ran : action heap with
  | none => simp [ran] at executed
  | some pair =>
    rcases pair with ⟨outcome, middle⟩
    cases outcome <;> simp [ran] at executed
    exact executed.1.symm

theorem heapify_returns_none (heap after : Heap) (values : List Value) (returned : Value)
    (executed : heapify values heap = some (.ok returned, after)) : returned = .scalar .none := by
  rcases values with _ | ⟨value, _ | ⟨extra, rest⟩⟩
  · simp [heapify, Mutable.error] at executed
  · cases value with
    | scalar scalar => simp [heapify, receiver, Mutable.error] at executed
    | ref address =>
      cases found : heap[address]? with
      | none => simp [heapify, receiver, items, found, Mutable.unsupported] at executed
      | some object =>
        cases object <;> try (solve | simp [heapify, receiver, items, found, Mutable.error] at executed)
        case list values =>
          apply constant_map_returns (siftAll address (heapifyOrder values.length)) heap after (.scalar .none) returned
          simpa [heapify, receiver_list heap address values found, items_list heap address values found] using executed
  · simp [heapify, Mutable.error] at executed

theorem heappush_returns_none (heap after : Heap) (values : List Value) (returned : Value)
    (executed : heappush values heap = some (.ok returned, after)) : returned = .scalar .none := by
  rcases values with _ | ⟨value, _ | ⟨item, _ | ⟨extra, rest⟩⟩⟩
  · simp [heappush, Mutable.error] at executed
  · simp [heappush, Mutable.error] at executed
  · cases value with
    | scalar scalar => simp [heappush, receiver, Mutable.error] at executed
    | ref address =>
      cases found : heap[address]? with
      | none => simp [heappush, receiver, items, found, Mutable.unsupported] at executed
      | some object =>
        cases object <;> try (solve | simp [heappush, receiver, items, found, Mutable.error] at executed)
        case list values =>
          apply constant_map_returns (siftDown address 0 values.length)
            (heap.set address (.list (values ++ [item]))) after (.scalar .none) returned
          simpa [heappush, receiver_list heap address values found, items_list heap address values found,
            Mutable.appendItem, found] using executed
  · simp [heappush, Mutable.error] at executed

theorem heappop_return_bounded (heap after : Heap) (closed : Closed heap) (values : List Value) (returned : Value)
    (executed : heappop values heap = some (.ok returned, after)) : returned.edge.Within heap.length := by
  rcases values with _ | ⟨value, _ | ⟨extra, rest⟩⟩
  · simp [heappop, Mutable.error] at executed
  · cases value with
    | scalar scalar => simp [heappop, receiver, Mutable.error] at executed
    | ref address =>
      cases found : heap[address]? with
      | none => simp [heappop, receiver, items, found, Mutable.unsupported] at executed
      | some object =>
        cases object <;> try (solve | simp [heappop, receiver, items, found, Mutable.error] at executed)
        case list values =>
          cases values with
          | nil =>
            have popped := popItem_list_selection heap address [] (-1) found
            simp [popSelection, Py.Builtin.Sequence.normalizeIndex] at popped
            simp [heappop, receiver_list heap address [] found, popped] at executed
          | cons root rest =>
            rw [heappop_returns_root heap after address root returned rest found executed]
            exact closed _ (List.mem_of_getElem? found) root (List.mem_cons_self ..)
  · simp [heappop, Mutable.error] at executed

end ReturnBounds
end FormalSW.PyAst.Heapq.Relocation
