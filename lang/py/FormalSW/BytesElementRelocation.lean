import lang.py.FormalSW.ByteValuesRelocation

/-! Immutable-byte element conversion preserves failures and unsupported custom indices. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

theorem RuntimeLayout.bytesElement {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (value : Value) (inside : value.edge.Within logical.length) :
    Mutable.bytesElement (relocateValue rename value) physical =
      (Mutable.bytesElement value logical).map (fun pair => (pair.1, physical)) := by
  cases value with
  | scalar scalar => exact byte_relocates logical physical rename (.scalar scalar)
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    cases object : logical[address] <;> simp only [object, relocateObject] at moved
    all_goals simp [Mutable.bytesElement, relocateValue, found, object, moved, Mutable.byte, Mutable.integer, error, unsupported]

theorem bytesElement_heap (heap after : Heap) (value : Value) (inside : value.edge.Within heap.length)
    (outcome : Except ExceptionObject UInt8) (executed : Mutable.bytesElement value heap = some (outcome, after)) : after = heap := by
  have paired := (RuntimeLayout.refl heap).bytesElement value inside
  simp only [relocateValue_id, executed, Option.map_some] at paired
  exact congrArg Prod.snd (Option.some.inj paired)

theorem RuntimeLayout.bytesElements_pair {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (items : List Value)
    (inside : ∀ value ∈ items, value.edge.Within logical.length) :
    ∃ outcome : Option (Except ExceptionObject (List UInt8)),
      items.mapM Mutable.bytesElement logical = outcome.map (fun result => (result, logical)) ∧
      (items.map (relocateValue rename)).mapM Mutable.bytesElement physical = outcome.map (fun result => (result, physical)) := by
  induction items with
  | nil => exact ⟨some (.ok []), rfl, rfl⟩
  | cons value items ih =>
    have firstInside := inside value (by simp)
    have paired := layout.bytesElement value firstInside
    cases first : Mutable.bytesElement value logical with
    | none =>
      exact ⟨none, by simp [List.mapM_cons, eval_bind, first],
        by simp [List.map_cons, List.mapM_cons, eval_bind, paired, first]⟩
    | some pair =>
      rcases pair with ⟨result, after⟩
      have same := bytesElement_heap logical after value firstInside result first
      subst after
      cases result with
      | error exception =>
        exact ⟨some (.error exception), by simp [List.mapM_cons, eval_bind, first],
          by simp [List.map_cons, List.mapM_cons, eval_bind, paired, first]⟩
      | ok byte =>
        obtain ⟨remaining, left, right⟩ := ih (fun item member => inside item (List.mem_cons_of_mem _ member))
        refine ⟨remaining.map (Except.map (byte :: ·)), ?_, ?_⟩
        · cases remaining with
          | none => simp [List.mapM_cons, eval_bind, first, left]
          | some outcome => cases outcome <;> simp [List.mapM_cons, eval_bind, first, left, Except.map]
        · cases remaining with
          | none => simp [List.map_cons, List.mapM_cons, eval_bind, paired, first, right, -List.mapM_map]
          | some outcome => cases outcome <;> simp [List.map_cons, List.mapM_cons, eval_bind, paired, first, right, Except.map, -List.mapM_map]

theorem RuntimeLayout.bytesElements {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (items : List Value)
    (inside : ∀ value ∈ items, value.edge.Within logical.length) :
    (items.map (relocateValue rename)).mapM Mutable.bytesElement physical =
      (items.mapM Mutable.bytesElement logical).map (fun pair => (pair.1, physical)) := by
  obtain ⟨outcome, left, right⟩ := layout.bytesElements_pair items inside
  rw [left, right]
  cases outcome <;> rfl

theorem bytesElements_heap (heap after : Heap) (items : List Value)
    (inside : ∀ value ∈ items, value.edge.Within heap.length) (outcome : Except ExceptionObject (List UInt8))
    (executed : items.mapM Mutable.bytesElement heap = some (outcome, after)) : after = heap := by
  obtain ⟨result, left, _⟩ := (RuntimeLayout.refl heap).bytesElements_pair items inside
  rw [left] at executed
  cases result with
  | none => cases executed
  | some result => exact (congrArg Prod.snd (Option.some.inj executed)).symm

end FormalSW.PyAst.Mutable.Relocation
