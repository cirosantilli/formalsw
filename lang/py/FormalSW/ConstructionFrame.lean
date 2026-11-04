import lang.py.FormalSW.CompositeHeapFrame
import lang.py.FormalSW.SetConstructionEffects
import lang.py.FormalSW.DictionaryConstructor

/-! Constructors may fill fresh objects while retaining the entire original heap prefix. -/
namespace FormalSW.PyAst.Heapq
open Mutable Mutable.Relocation
set_option Elab.async false

/-- Existing cells are unchanged; completed failures may retain newly allocated partial objects. -/
def PreservesPrefix (action : Eval α) : Prop :=
  ∀ heap outcome after, action heap = some (outcome, after) → heap <+: after

theorem prefix_append_invariant (before : Heap) : AppendInvariant (fun heap => before <+: heap) := by
  intro heap object previous
  exact previous.trans ⟨[object], rfl⟩

theorem prefix_fresh_update (before : Heap) (address : Nat) (fresh : before.length ≤ address) :
    UpdateInvariant address (fun heap => before <+: heap) := by
  rintro heap object ⟨extra, rfl⟩
  exact ⟨extra.set (address - before.length) object, (List.set_append_right address object fresh).symm⟩

theorem AppendInvariant.append_list (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (heap extra : Heap) (holds : invariant heap) : invariant (heap ++ extra) := by
  induction extra generalizing heap with
  | nil => simpa using holds
  | cons object extra ih =>
    simpa only [List.append_assoc, List.singleton_append] using ih (heap ++ [object]) (stable heap object holds)

theorem Preserves.of_prefix (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (action : Eval α) (preserved : PreservesPrefix action) : Preserves invariant action := by
  intro heap outcome after holds executed
  obtain ⟨extra, rfl⟩ := preserved heap outcome after executed
  exact stable.append_list invariant heap extra holds

theorem PreservesPrefix.readonly (action : Eval α)
    (same : ∀ heap outcome after, action heap = some (outcome, after) → after = heap) : PreservesPrefix action := by
  intro heap outcome after executed
  rw [same heap outcome after executed]
  exact ⟨[], by simp⟩

theorem PreservesPrefix.bind (first : Eval α) (next : α → Eval β)
    (firstKeeps : PreservesPrefix first) (nextKeeps : ∀ value, PreservesPrefix (next value)) :
    PreservesPrefix (first >>= next) := by
  intro heap outcome after executed
  exact Preserves.bind _ _ _
    (Preserves.of_prefix _ (prefix_append_invariant heap) first firstKeeps)
    (fun value => Preserves.of_prefix _ (prefix_append_invariant heap) (next value) (nextKeeps value))
    heap outcome after ⟨[], by simp⟩ executed

theorem Preserves.mapM {α β : Type} (invariant : Heap → Prop) (items : List α) (action : α → Eval β)
    (preserved : ∀ item ∈ items, Preserves invariant (action item)) : Preserves invariant (items.mapM action) := by
  induction items with
  | nil => exact Preserves.pure invariant []
  | cons item rest ih =>
    rw [List.mapM_cons]
    apply Preserves.bind _ _ _ (preserved item (by simp))
    intro value
    apply Preserves.bind _ _ _ (ih (fun item member => preserved item (by simp [member])))
    intro values
    exact Preserves.pure invariant (value :: values)

theorem preserves_setKey (invariant : Heap → Prop) (value : Value) : Preserves invariant (Mutable.setKey value) := by
  unfold Mutable.setKey
  with_reducible repeat' first
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | split

theorem allocateSetValues_prefix (items : List Value) : PreservesPrefix (Mutable.allocateSetValues items) := by
  intro heap outcome after executed
  rw [allocateSetValues_eq] at executed
  by_cases scalar : scalarValues items
  · have kept : Preserves (fun after => heap <+: after)
        (do let keys ← items.mapM Mutable.setKey; Mutable.allocateSet (keys.foldl ScalarSet.insert [])) :=
      Preserves.bind _ _ _ (Preserves.mapM _ items Mutable.setKey (fun item _ => preserves_setKey _ item))
        (fun _ => preserves_allocateSet _ (prefix_append_invariant heap) _)
    exact kept heap outcome after ⟨[], by simp⟩ (by simpa only [scalar, ↓reduceIte] using executed)
  · have kept : Preserves (fun after => heap <+: after) (do
        let _ ← Mutable.allocateSet []
        let _ ← items.mapM (Mutable.addItem heap.length)
        pure (.ref heap.length) : Eval Value) := by
      apply Preserves.bind _ _ _ (preserves_allocateSet _ (prefix_append_invariant heap) [])
      intro _
      apply Preserves.bind _ _ _ (Preserves.mapM _ items (Mutable.addItem heap.length)
        (fun item _ => preserves_addItem heap.length _ (prefix_fresh_update heap heap.length (Nat.le_refl _)) item))
      intro _
      exact Preserves.pure _ _
    apply kept heap outcome after ⟨[], by simp⟩
    simpa only [scalar, Bool.false_eq_true, ↓reduceIte, Mutable.eval_bind, Mutable.eval_get,
      Option.bind_eq_bind, Option.bind_some] using executed

theorem preserves_allocateSetValues (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (items : List Value) : Preserves invariant (Mutable.allocateSetValues items) :=
  Preserves.of_prefix invariant stable _ (allocateSetValues_prefix items)

theorem preserves_setSourceItems (invariant : Heap → Prop) (source : Value) :
    Preserves invariant (setSourceItems source) := by
  unfold setSourceItems
  with_reducible repeat' first
    | exact preserves_sequence invariant _
    | exact Preserves.pure invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | split

theorem preserves_setFrom (invariant : Heap → Prop) (stable : AppendInvariant invariant) (source : Value) :
    Preserves invariant (Mutable.setFrom source) := by
  rw [setFrom_eq]
  exact Preserves.bind _ _ _ (preserves_setSourceItems invariant source)
    (preserves_allocateSetValues invariant stable)

theorem preserves_dictionaryIterable (invariant : Heap → Prop) (source : Value) :
    Preserves invariant (DictionaryConstructor.iterable source) := by
  unfold DictionaryConstructor.iterable
  with_reducible repeat' first
    | exact preserves_sequence invariant _
    | exact Preserves.pure invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | split

theorem preserves_dictionaryInsertRow (address : Nat) (invariant : Heap → Prop)
    (stable : UpdateInvariant address invariant) (row : Value) :
    Preserves invariant (DictionaryConstructor.insertRow address row) := by
  unfold DictionaryConstructor.insertRow
  apply Preserves.bind _ _ _ (preserves_dictionaryIterable invariant row)
  intro items
  split
  · exact Preserves.bind _ _ _ (preserves_setItem address invariant stable _ _) (fun _ => Preserves.pure invariant ())
  · exact Preserves.error invariant "ValueError"

theorem preserves_dictionaryInsertRows (address : Nat) (invariant : Heap → Prop)
    (stable : UpdateInvariant address invariant) (rows : List Value) :
    Preserves invariant (DictionaryConstructor.insertRows address rows) := by
  induction rows with
  | nil => exact Preserves.pure invariant ()
  | cons row rest ih =>
    exact Preserves.bind _ _ _ (preserves_dictionaryInsertRow address invariant stable row) (fun _ => ih)

theorem dictionaryFromIterable_prefix (source : Value) : PreservesPrefix (DictionaryConstructor.fromIterable source) := by
  intro heap outcome after executed
  have kept : Preserves (fun after => heap <+: after) (do
      let _ ← Mutable.allocateDict []
      DictionaryConstructor.insertRows heap.length (← DictionaryConstructor.iterable source)
      pure (.ref heap.length) : Eval Value) := by
    apply Preserves.bind _ _ _ (preserves_allocateDict _ (prefix_append_invariant heap) [])
    intro _
    dsimp only
    with_reducible apply Preserves.bind _ _ _ (preserves_dictionaryIterable _ source)
    intro rows
    apply Preserves.bind _ _ _ (preserves_dictionaryInsertRows heap.length _
      (prefix_fresh_update heap heap.length (Nat.le_refl _)) rows)
    intro _
    exact Preserves.pure _ _
  apply kept heap outcome after ⟨[], by simp⟩
  simpa only [DictionaryConstructor.fromIterable, Mutable.eval_bind, Mutable.eval_get,
    Option.bind_eq_bind, Option.bind_some] using executed

theorem preserves_dictionaryFromIterable (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (source : Value) : Preserves invariant (DictionaryConstructor.fromIterable source) :=
  Preserves.of_prefix invariant stable _ (dictionaryFromIterable_prefix source)

theorem preserves_dictionaryConstruct (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (values : List Value) : Preserves invariant (DictionaryConstructor.construct values) := by
  unfold DictionaryConstructor.construct
  with_reducible repeat' first
    | exact preserves_allocateDict invariant stable _
    | exact preserves_dictionaryFromIterable invariant stable _
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | dsimp only
    | split

  all_goals
    apply Preserves.bind _ _ _ (Preserves.modify invariant _ (fun heap => stable heap _))
    intro ignored
    exact Preserves.pure invariant _

theorem dictionaryConstruct_prefix (values : List Value) : PreservesPrefix (DictionaryConstructor.construct values) := by
  intro heap outcome after executed
  exact preserves_dictionaryConstruct _ (prefix_append_invariant heap) values
    heap outcome after ⟨[], by simp⟩ executed

theorem preserves_setConstruct (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (values : List Value) : Preserves invariant (HeapCalls.primitive (.builtin .set) values) := by
  cases values with
  | nil => exact preserves_allocateSet invariant stable []
  | cons source rest =>
    cases rest with
    | nil => exact preserves_setFrom invariant stable source
    | cons => exact Preserves.error invariant "TypeError"

end FormalSW.PyAst.Heapq
