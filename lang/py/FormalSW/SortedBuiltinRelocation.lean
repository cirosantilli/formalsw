import lang.py.FormalSW.SortingRelocation
import lang.py.FormalSW.ListMethodRelocation
import lang.py.FormalSW.ListInplaceRelocation

/-! Ordinary sorted calls acquire stored set and dictionary representatives before reverse validation. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

/-- Unlike keyed callback acquisition, primitive sorting also accepts both set representations. -/
def sortedPool (source : Value) : Mutable.Eval (List Value) := do
  match source with
  | .ref address => match (← get)[address]? with
      | some (.set items) => pure (items.map Mutable.Value.scalar)
      | some (.keySet items) => pure (items.map Prod.snd)
      | some (.dict entries) => pure (entries.map fun entry => .scalar entry.1)
      | some (.keyDict entries) => pure (entries.map fun entry => entry.2.1)
      | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => Mutable.unsupported
      | _ => Mutable.sequence source
  | _ => Mutable.sequence source

theorem sortedPool_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (source : Value) (inside : source.edge.Within logical.length) :
    sortedPool (relocateValue rename source) physical =
      (sortedPool source logical).map (fun pair => (pair.1.map (List.map (relocateValue rename)), physical)) := by
  cases source with
  | scalar scalar => exact layout.sequence (.scalar scalar) inside
  | ref address =>
    have found := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    cases object : logical[address] <;> simp only [object, relocateObject] at moved <;>
      simp [sortedPool, Mutable.sequence, relocateValue, found, object, moved,
        Except.map, List.map_map, Function.comp_def, Mutable.unsupported]

theorem sortedPool_heap (heap after : Mutable.Heap) (source : Value) (inside : source.edge.Within heap.length)
    (outcome : Except ExceptionObject (List Value)) (executed : sortedPool source heap = some (outcome, after)) : after = heap := by
  have paired := sortedPool_relocates heap heap id (RuntimeLayout.refl heap) source inside
  simp only [relocateValue_id, executed, Option.map_some] at paired
  exact congrArg Prod.snd (Option.some.inj paired)

theorem sortedPool_bounded (heap after : Mutable.Heap) (closed : Closed heap) (source : Value)
    (items : List Value) (executed : sortedPool source heap = some (.ok items, after)) :
    ∀ item ∈ items, item.edge.Within heap.length := by
  cases source with
  | scalar scalar => exact sequence_items_within heap after closed (.scalar scalar) items executed
  | ref address =>
    cases found : heap[address]? with
    | none => simp [sortedPool, Mutable.sequence, found, Mutable.unsupported] at executed
    | some object =>
      have bounded := closed object (List.mem_of_getElem? found)
      cases object with
      | keySet entries =>
        simp [sortedPool, found] at executed
        rcases executed with ⟨rfl, rfl⟩
        exact bounded
      | set entries | dict entries =>
        simp [sortedPool, found] at executed
        rcases executed with ⟨rfl, rfl⟩
        intro item member
        obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
        trivial
      | keyDict entries =>
        simp [sortedPool, found] at executed
        rcases executed with ⟨rfl, rfl⟩
        intro item member
        obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
        exact bounded entry.2.1 (List.mem_flatMap.mpr ⟨entry, present, by simp⟩)
      | list entries | tuple entries | bytearray entries =>
        exact sequence_items_within heap after closed (.ref address) items
          (by simpa [sortedPool, found] using executed)
      | _ => simp [sortedPool, found, Mutable.unsupported] at executed

/-- Comparisons run before allocation and retain errors or unsupported outcomes. -/
def sortedValues (reverse : Bool) (items : List Value) : Mutable.Eval Value := do
  match HeapSort.sortWithReverse (← get) reverse items with
  | none => Mutable.unsupported
  | some (.ok ordered) => Mutable.allocate ordered
  | some (.error exception) => throw exception

def sortedPrimitive (hasReverse : Bool) : List Value → Mutable.Eval Value
  | [source] => if hasReverse then Mutable.error "TypeError" else do
      let items ← sortedPool source
      sortedValues false items
  | [source, reverse] => if hasReverse then do
      let items ← sortedPool source
      let direction ← sortDirection reverse
      sortedValues direction items
    else Mutable.unsupported
  | _ => if hasReverse then Mutable.error "TypeError" else Mutable.unsupported

private theorem sortedValues_direction (reverse : Value) (items : List Value) :
    (do
      if let .ref address := reverse then
        match (← get)[address]? with
        | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => Mutable.unsupported
        | _ => pure ()
      let direction ← Mutable.truth reverse
      sortedValues direction items) =
    (sortDirection reverse >>= fun direction => sortedValues direction items) := by
  cases reverse with
  | scalar scalar => rfl
  | ref address =>
    funext heap
    cases found : heap[address]? with
    | none => simp [sortDirection, Mutable.eval_bind, found] <;> rfl
    | some object => cases object <;> simp [sortDirection, Mutable.eval_bind, found, Mutable.unsupported] <;> rfl

theorem primitive_sorted_eq (hasReverse : Bool) (values : List Value) :
    primitive (.builtin (if hasReverse then .sortedReverse else .sorted)) values = sortedPrimitive hasReverse values := by
  cases hasReverse <;> funext heap
  all_goals rcases values with _ | ⟨source, _ | ⟨reverse, _ | ⟨extra, rest⟩⟩⟩
  all_goals try rfl
  all_goals cases source with
    | scalar scalar =>
      simp only [primitive, sortedPrimitive, sortedPool, Bool.false_eq_true, ↓reduceIte,
        ← sortedValues_direction]
      rfl
    | ref address =>
      cases found : heap[address]? with
      | none => simp [primitive, sortedPrimitive, sortedPool, Mutable.eval_bind, found, Mutable.sequence, Mutable.unsupported]
      | some object =>
        cases object <;> simp [primitive, sortedPrimitive, sortedPool, Mutable.eval_bind, found, Mutable.sequence, Mutable.unsupported]
        all_goals first
          | rfl
          | cases reverse with
            | scalar flag => simp [sortDirection, sortedValues, Mutable.eval_bind] <;> rfl
            | ref position =>
              cases reverseFound : heap[position]? with
              | none => simp [sortDirection, sortedValues, Mutable.eval_bind, reverseFound] <;> rfl
              | some reverseObject => cases reverseObject <;>
                  simp [sortDirection, sortedValues, Mutable.eval_bind, reverseFound, Mutable.unsupported] <;> rfl

end FormalSW.PyAst.HeapCalls.Relocation
