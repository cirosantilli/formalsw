import lang.py.FormalSW.ItemWriteRelocation

/-! Buffer element conversion preserves its first error without changing memory. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

theorem bytes_mapM_pair (logical physical : Heap) (rename : Nat → Nat) (items : List Value) :
    ∃ outcome,
      items.mapM Mutable.byte logical = some (outcome, logical) ∧
      (items.map (relocateValue rename)).mapM Mutable.byte physical = some (outcome, physical) := by
  induction items with
  | nil => exact ⟨.ok [], rfl, rfl⟩
  | cons value items ih =>
    obtain ⟨first, converted⟩ := byte_total logical value
    have paired := byte_relocates logical physical rename value
    obtain ⟨rest, left, right⟩ := ih
    cases first with
    | error exception =>
      exact ⟨.error exception, by simp [List.mapM_cons, eval_bind, converted],
        by simp [List.map_cons, List.mapM_cons, eval_bind, paired, converted]⟩
    | ok byte =>
      cases rest with
      | error exception =>
        exact ⟨.error exception, by simp [List.mapM_cons, eval_bind, converted, left, Except.map],
          by simp [List.map_cons, List.mapM_cons, eval_bind, paired, converted, right, Except.map, -List.mapM_map]⟩
      | ok bytes =>
        exact ⟨.ok (byte :: bytes), by simp [List.mapM_cons, eval_bind, converted, left, Except.map],
          by simp [List.map_cons, List.mapM_cons, eval_bind, paired, converted, right, Except.map, -List.mapM_map]⟩

theorem RuntimeLayout.byteValues {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (value : Value) (inside : value.edge.Within logical.length) :
    Mutable.byteValues (relocateValue rename value) physical =
      (Mutable.byteValues value logical).map (fun pair => (pair.1, physical)) := by
  cases value with
  | scalar scalar => cases scalar <;> rfl
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    cases object : logical[address] <;> simp only [object, relocateObject] at moved
    case list items =>
      obtain ⟨outcome, left, right⟩ := bytes_mapM_pair logical physical rename items
      simp [Mutable.byteValues, relocateValue, found, object, moved, left, right, -List.mapM_map]
    case tuple items =>
      obtain ⟨outcome, left, right⟩ := bytes_mapM_pair logical physical rename items
      simp [Mutable.byteValues, relocateValue, found, object, moved, left, right, -List.mapM_map]
    all_goals simp [Mutable.byteValues, relocateValue, found, object, moved, error, unsupported]

theorem byteValues_heap (heap after : Heap) (value : Value) (outcome : Except ExceptionObject (List UInt8))
    (executed : Mutable.byteValues value heap = some (outcome, after)) : after = heap := by
  cases value with
  | scalar scalar =>
    cases scalar <;> simp [Mutable.byteValues, error] at executed
    all_goals exact executed.2.symm
  | ref address =>
    cases found : heap[address]? with
    | none => simp [Mutable.byteValues, found, unsupported] at executed
    | some object =>
      cases object with
      | list items | tuple items =>
        obtain ⟨answer, left, _⟩ := bytes_mapM_pair heap heap id items
        have same : answer = outcome ∧ heap = after := by simpa [Mutable.byteValues, found, left] using executed
        exact same.2.symm
      | bytearray bytes | dict entries | keyDict entries | set items | keySet items
      | «instance» origin name fields | dataInstance origin name frozen declared fields =>
        simp [Mutable.byteValues, found, unsupported, error] at executed
        all_goals exact executed.2.symm

end FormalSW.PyAst.Mutable.Relocation
