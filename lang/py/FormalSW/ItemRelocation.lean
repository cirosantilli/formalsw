import lang.py.FormalSW.DictionaryRelocation
import lang.py.FormalSW.SequenceRelocation

/-! Indexed reads retain aliases and every modeled outcome across allocation layouts. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

theorem RuntimeLayout.getItem (logical physical : Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (receiver subscript : Value) (receiverInside : receiver.edge.Within logical.length)
    (indexInside : subscript.edge.Within logical.length) :
    Mutable.getItem (relocateValue rename receiver) (relocateValue rename subscript) physical =
      (Mutable.getItem receiver subscript logical).map
        (fun result => (result.1.map (relocateValue rename), physical)) := by
  cases receiver with
  | scalar value =>
    cases subscript with
    | ref address => simp [Mutable.getItem, relocateValue, Mutable.error, Except.map]
    | scalar index =>
      cases selected : Strings.get value index <;>
        simp [Mutable.getItem, relocateValue, selected, Except.map]
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem receiverInside
    cases object : logical[address] with
    | list items => exact layout.getItem_list address items subscript (found.trans (congrArg some object))
    | tuple items => exact layout.getItem_tuple address items subscript (found.trans (congrArg some object))
    | dict entries => exact layout.getItem_dict closed address entries subscript (found.trans (congrArg some object)) indexInside
    | keyDict entries => exact layout.getItem_keyDict closed address entries subscript (found.trans (congrArg some object)) indexInside
    | bytearray bytes =>
      have actual := found.trans (congrArg some object)
      have moved := layout.lookup address _ actual
      have paired := index_relocates bytes bytes rfl subscript rename logical physical
      simp only [relocateValue] at paired
      obtain ⟨outcome, indexed, _⟩ := index_total bytes subscript logical
      cases outcome <;>
        simp [Mutable.getItem, relocateValue, actual, moved, relocateObject, paired, indexed, eval_bind, Except.map]
    | _ =>
      have actual := found.trans (congrArg some object)
      have moved := layout.lookup address _ actual
      simp [Mutable.getItem, relocateValue, actual, moved, relocateObject, Mutable.error, Except.map]

theorem getItem_bounded (heap after : Heap) (closed : Closed heap) (receiver subscript value : Value)
    (receiverInside : receiver.edge.Within heap.length)
    (executed : Mutable.getItem receiver subscript heap = some (.ok value, after)) :
    value.edge.Within heap.length := by
  cases receiver with
  | scalar scalar =>
    cases subscript with
    | ref address => simp [Mutable.getItem, Mutable.error] at executed
    | scalar index =>
      cases selected : Strings.get scalar index with
      | error exception => simp [Mutable.getItem, selected] at executed
      | ok result =>
        have same : Value.scalar result = value ∧ heap = after := by
          simpa [Mutable.getItem, selected] using executed
        rw [← same.1]
        trivial
  | ref address =>
    have found : heap[address]? = some heap[address] := List.getElem?_eq_getElem receiverInside
    cases object : heap[address] with
    | list items | tuple items =>
      have actual := found.trans (congrArg some object)
      apply indexedRead_bounded heap after items subscript value (closed _ (List.mem_of_getElem? actual))
      simpa [Mutable.getItem, actual, Except.map] using executed
    | dict entries =>
      exact getItem_dict_bounded heap after closed address entries subscript value
        (found.trans (congrArg some object)) executed
    | keyDict entries =>
      exact getItem_keyDict_bounded heap after closed address entries subscript value
        (found.trans (congrArg some object)) executed
    | bytearray bytes =>
      have actual := found.trans (congrArg some object)
      obtain ⟨outcome, indexed, _⟩ := index_total bytes subscript heap
      cases outcome with
      | error exception => simp [Mutable.getItem, actual, indexed, eval_bind, Except.map] at executed
      | ok position =>
        have same : Value.scalar (.int ((bytes[position]?).getD 0).toNat) = value ∧ heap = after := by
          simpa [Mutable.getItem, actual, indexed, eval_bind, Except.map] using executed
        rw [← same.1]
        trivial
    | _ => simp [Mutable.getItem, found, object, Mutable.error] at executed

theorem getItem_effect (heap after : Heap) (closed : Closed heap) (receiver subscript : Value)
    (receiverInside : receiver.edge.Within heap.length) (indexInside : subscript.edge.Within heap.length)
    (outcome : Except ExceptionObject Value)
    (executed : Mutable.getItem receiver subscript heap = some (outcome, after)) :
    after = heap ∧ ∀ value, outcome = .ok value → value.edge.Within heap.length := by
  have stationary := RuntimeLayout.getItem heap heap id (RuntimeLayout.refl heap) closed
    receiver subscript receiverInside indexInside
  simp only [relocateValue_id, executed, Option.map_some] at stationary
  have unchanged : after = heap := congrArg Prod.snd (Option.some.inj stationary)
  refine ⟨unchanged, ?_⟩
  intro value success
  subst outcome
  exact getItem_bounded heap after closed receiver subscript value receiverInside executed

end FormalSW.PyAst.Mutable.Relocation
