import lang.py.FormalSW.MutationRelocation
import lang.py.FormalSW.ComparisonComplete
import lang.py.FormalSW.HeapqPreservation

/-! Heap sifts retain aliases, comparison outcomes and partial mutations across layouts. -/
namespace FormalSW.PyAst.Heapq.Relocation
open Mutable.Relocation
set_option Elab.async false

variable {logical physical : Heap} {rename : Nat → Nat}

theorem items_relocates (layout : RuntimeLayout logical physical rename)
    (address : Nat) (inside : address < logical.length) :
    items (rename address) physical = (items address logical).map
      (fun pair => (pair.1.map (List.map (relocateValue rename)), physical)) := by
  have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
  have moved := layout.lookup address _ found
  cases object : logical[address] <;>
    simp [items, found, moved, object, relocateObject, Mutable.error, Except.map]

theorem atIndex_relocates (layout : RuntimeLayout logical physical rename)
    (address position : Nat) (inside : address < logical.length) :
    atIndex (rename address) position physical = (atIndex address position logical).map
      (fun pair => (pair.1.map (relocateValue rename), physical)) := by
  have moved := items_relocates layout address inside
  cases read : items address logical with
  | none => simp [atIndex, moved, read, Mutable.eval_bind]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    obtain rfl := preserves_items (fun after => after = logical) address logical outcome after rfl read
    cases outcome with
    | error exception => simp [atIndex, moved, read, Mutable.eval_bind, Except.map]
    | ok values =>
      cases selected : values[position]? <;>
        simp [atIndex, moved, read, Mutable.eval_bind, Except.map, selected, Mutable.error]

theorem atIndex_bounded (heap after : Heap) (address position : Nat) (value : Value)
    (closed : Closed heap) (read : atIndex address position heap = some (.ok value, after)) :
    value.edge.Within heap.length := by
  cases found : heap[address]? with
  | none => simp [atIndex, items, found, Mutable.unsupported] at read
  | some object =>
    cases object <;> simp [atIndex, items, found, Mutable.error] at read
    case list values =>
      cases selected : values[position]? with
      | none => simp [selected] at read
      | some item =>
        simp [selected] at read
        exact read.1 ▸ closed _ (List.mem_of_getElem? found) item (List.mem_of_getElem? selected)

theorem less_relocates (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (left right : Value) (leftInside : left.edge.Within logical.length)
    (rightInside : right.edge.Within logical.length) :
    less (relocateValue rename left) (relocateValue rename right) physical =
      (less left right logical).map (fun pair => (pair.1, physical)) := by
  have compared := layout.compare_native closed false left right leftInside rightInside
  simp only [less, Mutable.eval_bind, Mutable.eval_get, Option.bind_eq_bind, Option.bind_some, compared]
  cases HeapSort.compare (HeapSort.comparisonFuel logical) logical false left right with
  | none => rfl
  | some outcome => cases outcome <;> rfl

theorem swap_relocates (layout : ExecutionLayout logical physical rename)
    (address left right : Nat) (inside : address < logical.length) :
    MutationRelocates logical physical rename id (swap address left right) (swap (rename address) left right) := by
  have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
  have moved := layout.runtime.lookup address _ found
  cases object : logical[address] <;> try
    (simp [MutationRelocates, swap, items, found, object, moved, relocateObject, Mutable.error, Except.map]
     exact layout)
  case list values =>
    rw [object] at found moved
    by_cases hl : left < values.length
    · by_cases hr : right < values.length
      · have first := swap_list logical address left right values found hl hr
        have second := swap_list physical (rename address) left right (values.map (relocateValue rename))
          moved (by simpa using hl) (by simpa using hr)
        have bounded := layout.closed _ (List.mem_of_getElem? found)
        have updated : ∀ value ∈ (values.set left values[right]).set right values[left],
            value.edge.Within logical.length := by
          intro value member
          rcases List.mem_or_eq_of_mem_set member with member | rfl
          · rcases List.mem_or_eq_of_mem_set member with member | rfl
            · exact bounded value member
            · exact bounded _ (List.getElem_mem hr)
          · exact bounded _ (List.getElem_mem hl)
        simp only [MutationRelocates, first]
        refine ⟨_, ?_, layout.set_list address values _ found updated, by simp, by simp⟩
        simpa only [Except.map, id_eq, List.getElem_map, List.map_set] using second
      · simp [MutationRelocates, swap, items, found, moved, relocateObject,
          List.getElem?_eq_none (Nat.le_of_not_gt hr), Mutable.error, Except.map]
        exact layout
    · simp [MutationRelocates, swap, items, found, moved, relocateObject,
        List.getElem?_eq_none (Nat.le_of_not_gt hl), Mutable.error, Except.map]
      exact layout

theorem atIndex_bind_relocates {α β : Type} (layout : ExecutionLayout logical physical rename)
    (address position : Nat) (inside : address < logical.length) (convert : α → β)
    (next : Value → Eval α) (otherNext : Value → Eval β)
    (following : ∀ value, value.edge.Within logical.length →
      MutationRelocates logical physical rename convert (next value) (otherNext (relocateValue rename value))) :
    MutationRelocates logical physical rename convert (atIndex address position >>= next)
      (atIndex (rename address) position >>= otherNext) := by
  apply MutationRelocates.readonly_bind layout (relocateValue rename) convert _ _ _ _
    (atIndex_relocates layout.runtime address position inside)
    (fun outcome after read => preserves_atIndex (fun after => after = logical) address position
      logical outcome after rfl read)
  intro value read
  exact following value (atIndex_bounded logical logical address position value layout.closed read)

theorem less_bind_relocates {α β : Type} (layout : ExecutionLayout logical physical rename)
    (left right : Value) (leftInside : left.edge.Within logical.length)
    (rightInside : right.edge.Within logical.length) (convert : α → β)
    (next : Bool → Eval α) (otherNext : Bool → Eval β)
    (following : ∀ answer, MutationRelocates logical physical rename convert (next answer) (otherNext answer)) :
    MutationRelocates logical physical rename convert (less left right >>= next)
      (less (relocateValue rename left) (relocateValue rename right) >>= otherNext) := by
  apply MutationRelocates.readonly_bind layout id convert _ _ _ _
    (by simpa only [Except.map_id] using less_relocates layout.runtime layout.closed left right leftInside rightInside)
    (fun outcome after read => preserves_less (fun after => after = logical) left right
      logical outcome after rfl read)
  exact fun answer _ => following answer

theorem siftDown_relocates {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename)
    (address start position : Nat) (inside : address < logical.length) :
    MutationRelocates logical physical rename id (siftDown address start position)
      (siftDown (rename address) start position) := by
  conv => arg 5; rw [siftDown]
  conv => arg 6; rw [siftDown]
  by_cases moving : start < position
  · simp only [moving, ↓reduceIte]
    apply atIndex_bind_relocates layout address position inside id
    intro value valueInside
    apply atIndex_bind_relocates layout address ((position - 1) / 2) inside id
    intro above aboveInside
    apply less_bind_relocates layout value above valueInside aboveInside id
    intro smaller
    cases smaller with
    | false => exact MutationRelocates.pure layout id ()
    | true =>
      apply MutationRelocates.bind id id _ _ _ _ (swap_relocates layout address position ((position - 1) / 2) inside)
      intro _ middle other _ retained length _
      exact siftDown_relocates retained address start ((position - 1) / 2) (by omega)
  · simp only [moving, ↓reduceIte]
    exact MutationRelocates.pure layout id ()
termination_by position
decreasing_by
  have := Nat.div_le_self (position - 1) 2
  omega

theorem siftChildren_relocates {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename)
    (address size start position : Nat) (inside : address < logical.length) :
    MutationRelocates logical physical rename id (siftChildren address size start position)
      (siftChildren (rename address) size start position) := by
  conv => arg 5; rw [siftChildren]
  conv => arg 6; rw [siftChildren]
  dsimp only
  by_cases children : 2 * position + 1 < size
  · simp only [children, ↓reduceIte]
    by_cases both : 2 * position + 1 + 1 < size
    · simp only [both, ↓reduceIte]
      apply atIndex_bind_relocates layout address (2 * position + 1) inside id
      intro left leftInside
      apply atIndex_bind_relocates layout address (2 * position + 1 + 1) inside id
      intro right rightInside
      apply less_bind_relocates layout left right leftInside rightInside id
      intro smaller
      cases smaller with
      | false =>
        apply MutationRelocates.bind id id _ _ _ _ (swap_relocates layout address position (2 * position + 1 + 1) inside)
        intro _ middle other _ retained length _
        exact siftChildren_relocates retained address size start (2 * position + 1 + 1) (by omega)
      | true =>
        apply MutationRelocates.bind id id _ _ _ _ (swap_relocates layout address position (2 * position + 1) inside)
        intro _ middle other _ retained length _
        exact siftChildren_relocates retained address size start (2 * position + 1) (by omega)
    · simp only [both, ↓reduceIte]
      apply MutationRelocates.bind id id _ _ _ _ (swap_relocates layout address position (2 * position + 1) inside)
      intro _ middle other _ retained length _
      exact siftChildren_relocates retained address size start (2 * position + 1) (by omega)
  · simp only [children, ↓reduceIte]
    exact siftDown_relocates layout address start position inside
termination_by size - position
decreasing_by all_goals omega

theorem siftUp_relocates (layout : ExecutionLayout logical physical rename)
    (address position : Nat) (inside : address < logical.length) :
    MutationRelocates logical physical rename id (siftUp address position) (siftUp (rename address) position) := by
  apply MutationRelocates.readonly_bind layout (List.map (relocateValue rename)) id _ _ _ _
    (items_relocates layout.runtime address inside)
    (fun outcome after read => preserves_items (fun after => after = logical) address logical outcome after rfl read)
  intro values _
  simp only [List.length_map]
  split
  · exact siftChildren_relocates layout address values.length position position inside
  · exact MutationRelocates.error layout id "IndexError"

theorem siftAll_relocates (layout : ExecutionLayout logical physical rename)
    (address : Nat) (positions : List Nat) (inside : address < logical.length) :
    MutationRelocates logical physical rename id (siftAll address positions) (siftAll (rename address) positions) := by
  induction positions generalizing logical physical with
  | nil => exact MutationRelocates.pure layout id ()
  | cons position rest ih =>
    apply MutationRelocates.bind id id _ _ _ _ (siftUp_relocates layout address position inside)
    intro _ middle other _ retained length _
    exact ih retained (by omega)

end FormalSW.PyAst.Heapq.Relocation
