import lang.py.FormalSW.ComparisonComplete

/-! Stable sorting retains item identities and every comparison outcome across layouts. -/
namespace FormalSW.PyAst
set_option Elab.async false

namespace HeapSort

theorem insert_perm (heap : Heap) (value : Value) (items ordered : List Value)
    (executed : insert heap value items = some (.ok ordered)) : ordered.Perm (value :: items) := by
  induction items generalizing ordered with
  | nil =>
    simp [insert] at executed
    subst ordered
    exact .refl _
  | cons first rest ih =>
    cases compared : compare (comparisonFuel heap) heap false first value with
    | none => simp [insert, compared] at executed
    | some outcome =>
      cases outcome with
      | error exception => simp [insert, compared] at executed
      | ok smaller =>
        cases smaller with
        | false =>
          simp [insert, compared] at executed
          subst ordered
          exact .refl _
        | true =>
          cases inserted : insert heap value rest with
          | none => simp [insert, compared, inserted] at executed
          | some result =>
            cases result with
            | error exception => simp [insert, compared, inserted, Except.map] at executed
            | ok tail =>
              simp [insert, compared, inserted, Except.map] at executed
              subst ordered
              exact ((ih tail inserted).cons first).trans (.swap _ _ _)

theorem sort_perm (heap : Heap) (items ordered : List Value)
    (executed : sort heap items = some (.ok ordered)) : ordered.Perm items := by
  induction items generalizing ordered with
  | nil =>
    simp [sort] at executed
    subst ordered
    exact .refl _
  | cons first rest ih =>
    cases sorted : sort heap rest with
    | none => simp [sort, sorted] at executed
    | some result =>
      cases result with
      | error exception => simp [sort, sorted] at executed
      | ok tail =>
        have inserted : insert heap first tail = some (.ok ordered) := by
          simpa [sort, sorted] using executed
        exact (insert_perm heap first tail ordered inserted).trans ((ih tail sorted).cons first)

theorem sortWithReverse_perm (heap : Heap) (reverse : Bool) (items ordered : List Value)
    (executed : sortWithReverse heap reverse items = some (.ok ordered)) : ordered.Perm items := by
  cases reverse with
  | false => exact sort_perm heap items ordered executed
  | true =>
    cases sorted : sort heap items.reverse with
    | none => simp [sortWithReverse, sorted] at executed
    | some result =>
      cases result with
      | error exception => simp [sortWithReverse, sorted, Except.map] at executed
      | ok tail =>
        simp [sortWithReverse, sorted, Except.map] at executed
        subst ordered
        exact (List.reverse_perm tail).trans ((sort_perm heap items.reverse tail sorted).trans (List.reverse_perm items))

theorem keyedInsert_perm (heap : Heap) (value : (Value × Value)) (items ordered : List (Value × Value))
    (executed : keyedInsert heap value items = some (.ok ordered)) : ordered.Perm (value :: items) := by
  induction items generalizing ordered with
  | nil =>
    simp [keyedInsert] at executed
    subst ordered
    exact .refl _
  | cons first rest ih =>
    cases compared : compare (comparisonFuel heap) heap false first.2 value.2 with
    | none => simp [keyedInsert, compared] at executed
    | some outcome =>
      cases outcome with
      | error exception => simp [keyedInsert, compared] at executed
      | ok smaller =>
        cases smaller with
        | false =>
          simp [keyedInsert, compared] at executed
          subst ordered
          exact .refl _
        | true =>
          cases inserted : keyedInsert heap value rest with
          | none => simp [keyedInsert, compared, inserted] at executed
          | some result =>
            cases result with
            | error exception => simp [keyedInsert, compared, inserted, Except.map] at executed
            | ok tail =>
              simp [keyedInsert, compared, inserted, Except.map] at executed
              subst ordered
              exact ((ih tail inserted).cons first).trans (.swap _ _ _)

theorem keyedSort_perm (heap : Heap) (items ordered : List (Value × Value))
    (executed : keyedSort heap items = some (.ok ordered)) : ordered.Perm items := by
  induction items generalizing ordered with
  | nil =>
    simp [keyedSort] at executed
    subst ordered
    exact .refl _
  | cons first rest ih =>
    cases sorted : keyedSort heap rest with
    | none => simp [keyedSort, sorted] at executed
    | some result =>
      cases result with
      | error exception => simp [keyedSort, sorted] at executed
      | ok tail =>
        have inserted : keyedInsert heap first tail = some (.ok ordered) := by
          simpa [keyedSort, sorted] using executed
        exact (keyedInsert_perm heap first tail ordered inserted).trans ((ih tail sorted).cons first)

theorem keyedSortWithReverse_perm (heap : Heap) (reverse : Bool) (items ordered : List (Value × Value))
    (executed : keyedSortWithReverse heap reverse items = some (.ok ordered)) : ordered.Perm items := by
  cases reverse with
  | false => exact keyedSort_perm heap items ordered executed
  | true =>
    cases sorted : keyedSort heap items.reverse with
    | none => simp [keyedSortWithReverse, sorted] at executed
    | some result =>
      cases result with
      | error exception => simp [keyedSortWithReverse, sorted, Except.map] at executed
      | ok tail =>
        simp [keyedSortWithReverse, sorted, Except.map] at executed
        subst ordered
        exact (List.reverse_perm tail).trans ((keyedSort_perm heap items.reverse tail sorted).trans (List.reverse_perm items))

end HeapSort

namespace Mutable.Relocation

theorem RuntimeLayout.insert {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (value : Value) (items : List Value) (valueInside : value.edge.Within logical.length)
    (itemsInside : ∀ item ∈ items, item.edge.Within logical.length) :
    HeapSort.insert physical ((relocateValue rename) value) (items.map (relocateValue rename)) =
      (HeapSort.insert logical value items).map (Except.map (List.map (relocateValue rename))) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    have headInside := itemsInside first (by simp)
    have tailInside : ∀ item ∈ rest, item.edge.Within logical.length :=
      fun item member => itemsInside item (List.mem_cons_of_mem _ member)
    have paired := layout.compare_native closed false first value headInside valueInside
    simp only [List.map_cons, HeapSort.insert, paired]
    cases compared : HeapSort.compare (HeapSort.comparisonFuel logical) logical false first value with
    | none => rfl
    | some outcome =>
      cases outcome with
      | error exception => rfl
      | ok smaller =>
        cases smaller with
        | false => rfl
        | true =>
          rw [ih tailInside]
          cases HeapSort.insert logical value rest with
          | none => rfl
          | some result => cases result <;> rfl

theorem RuntimeLayout.sort {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (items : List Value) (itemsInside : ∀ item ∈ items, item.edge.Within logical.length) :
    HeapSort.sort physical (items.map (relocateValue rename)) =
      (HeapSort.sort logical items).map (Except.map (List.map (relocateValue rename))) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    have headInside := itemsInside first (by simp)
    have tailInside : ∀ item ∈ rest, item.edge.Within logical.length :=
      fun item member => itemsInside item (List.mem_cons_of_mem _ member)
    simp only [List.map_cons, HeapSort.sort, ih tailInside]
    cases sorted : HeapSort.sort logical rest with
    | none => rfl
    | some outcome =>
      cases outcome with
      | error exception => rfl
      | ok ordered =>
        have bounded : ∀ item ∈ ordered, item.edge.Within logical.length :=
          fun item member => tailInside item ((HeapSort.sort_perm logical rest ordered sorted).mem_iff.mp member)
        exact layout.insert closed first ordered headInside bounded

theorem RuntimeLayout.sortWithReverse {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (reverse : Bool) (items : List Value) (itemsInside : ∀ item ∈ items, item.edge.Within logical.length) :
    HeapSort.sortWithReverse physical reverse (items.map (relocateValue rename)) =
      (HeapSort.sortWithReverse logical reverse items).map (Except.map (List.map (relocateValue rename))) := by
  cases reverse with
  | false => exact layout.sort closed items itemsInside
  | true =>
    have bounded : ∀ item ∈ items.reverse, item.edge.Within logical.length :=
      fun item member => itemsInside item (List.mem_reverse.mp member)
    simp only [HeapSort.sortWithReverse, ↓reduceIte, ← List.map_reverse, layout.sort closed items.reverse bounded]
    cases HeapSort.sort logical items.reverse with
    | none => rfl
    | some outcome => cases outcome <;> simp [Except.map, List.map_reverse]

theorem RuntimeLayout.keyedInsert {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (value : (Value × Value)) (items : List (Value × Value)) (valueInside : value.1.edge.Within logical.length ∧ value.2.edge.Within logical.length)
    (itemsInside : ∀ item ∈ items, item.1.edge.Within logical.length ∧ item.2.edge.Within logical.length) :
    HeapSort.keyedInsert physical ((Prod.map (relocateValue rename) (relocateValue rename)) value) (items.map (Prod.map (relocateValue rename) (relocateValue rename))) =
      (HeapSort.keyedInsert logical value items).map (Except.map (List.map (Prod.map (relocateValue rename) (relocateValue rename)))) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    have headInside := itemsInside first (by simp)
    have tailInside : ∀ item ∈ rest, item.1.edge.Within logical.length ∧ item.2.edge.Within logical.length :=
      fun item member => itemsInside item (List.mem_cons_of_mem _ member)
    have paired := layout.compare_native closed false first.2 value.2 headInside.2 valueInside.2
    simp only [List.map_cons, HeapSort.keyedInsert, Prod.map, paired]
    cases compared : HeapSort.compare (HeapSort.comparisonFuel logical) logical false first.2 value.2 with
    | none => rfl
    | some outcome =>
      cases outcome with
      | error exception => rfl
      | ok smaller =>
        cases smaller with
        | false => rfl
        | true =>
          have inserted := ih tailInside
          simp only [Prod.map] at inserted
          rw [inserted]
          cases HeapSort.keyedInsert logical value rest with
          | none => rfl
          | some result => cases result <;> rfl

theorem RuntimeLayout.keyedSort {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (items : List (Value × Value)) (itemsInside : ∀ item ∈ items, item.1.edge.Within logical.length ∧ item.2.edge.Within logical.length) :
    HeapSort.keyedSort physical (items.map (Prod.map (relocateValue rename) (relocateValue rename))) =
      (HeapSort.keyedSort logical items).map (Except.map (List.map (Prod.map (relocateValue rename) (relocateValue rename)))) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    have headInside := itemsInside first (by simp)
    have tailInside : ∀ item ∈ rest, item.1.edge.Within logical.length ∧ item.2.edge.Within logical.length :=
      fun item member => itemsInside item (List.mem_cons_of_mem _ member)
    simp only [List.map_cons, HeapSort.keyedSort, ih tailInside]
    cases sorted : HeapSort.keyedSort logical rest with
    | none => rfl
    | some outcome =>
      cases outcome with
      | error exception => rfl
      | ok ordered =>
        have bounded : ∀ item ∈ ordered, item.1.edge.Within logical.length ∧ item.2.edge.Within logical.length :=
          fun item member => tailInside item ((HeapSort.keyedSort_perm logical rest ordered sorted).mem_iff.mp member)
        exact layout.keyedInsert closed first ordered headInside bounded

theorem RuntimeLayout.keyedSortWithReverse {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (reverse : Bool) (items : List (Value × Value)) (itemsInside : ∀ item ∈ items, item.1.edge.Within logical.length ∧ item.2.edge.Within logical.length) :
    HeapSort.keyedSortWithReverse physical reverse (items.map (Prod.map (relocateValue rename) (relocateValue rename))) =
      (HeapSort.keyedSortWithReverse logical reverse items).map (Except.map (List.map (Prod.map (relocateValue rename) (relocateValue rename)))) := by
  cases reverse with
  | false => exact layout.keyedSort closed items itemsInside
  | true =>
    have bounded : ∀ item ∈ items.reverse, item.1.edge.Within logical.length ∧ item.2.edge.Within logical.length :=
      fun item member => itemsInside item (List.mem_reverse.mp member)
    simp only [HeapSort.keyedSortWithReverse, ↓reduceIte, ← List.map_reverse, layout.keyedSort closed items.reverse bounded]
    cases HeapSort.keyedSort logical items.reverse with
    | none => rfl
    | some outcome => cases outcome <;> simp [Except.map, List.map_reverse]

end Mutable.Relocation
end FormalSW.PyAst
