import lang.py.FormalSW.SequenceMembershipRelocation
import lang.py.FormalSW.ConstructionRelocation
import lang.py.FormalSW.ArithmeticRelocation

/-! List counting retains identity shortcuts; scalar sorting keeps Python's stable ordering. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem countElements_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (needle : Value) (items : List Value)
    (needleInside : needle.edge.Within logical.length) (itemsInside : ∀ value ∈ items, value.edge.Within logical.length) :
    countElements (relocateValue rename needle) (items.map (relocateValue rename)) = countElements needle items := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    have same := relocateValue_eq_iff logical.length rename layout.injective item needle (itemsInside item (by simp)) needleInside
    have tail := ih (fun value member => itemsInside value (List.mem_cons_of_mem _ member))
    simp only [List.map_cons, countElements, same, tail]
    cases item <;> cases needle <;> rfl

theorem scalarValues_all (items : List Value) :
    scalarValues items = items.all (fun | .scalar _ => true | .ref _ => false) := by
  induction items with
  | nil => rfl
  | cons item items ih => cases item <;> simp [scalarValues, ih]

def sortedScalars (reverse : Bool) (items : List Constant) : Except ExceptionObject (List Constant) :=
  if reverse then (ScalarSort.sort items.reverse).map List.reverse else ScalarSort.sort items

theorem sortWithReverse_scalars (heap : Mutable.Heap) (reverse : Bool) (items : List Constant) :
    HeapSort.sortWithReverse heap reverse (items.map Mutable.Value.scalar) =
      some ((sortedScalars reverse items).map (List.map Mutable.Value.scalar)) := by
  cases reverse with
  | false => exact HeapSort.sort_scalars heap items
  | true =>
    simp only [HeapSort.sortWithReverse, sortedScalars, ↓reduceIte, ← List.map_reverse, HeapSort.sort_scalars, Option.map_some]
    cases ScalarSort.sort items.reverse <;> simp [Except.map, List.map_reverse]

def sortDirection (value : Value) : Mutable.Eval Bool := do
  if let .ref address := value then
    match (← get)[address]? with
    | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => Mutable.unsupported
    | _ => pure ()
  Mutable.truth value

theorem sortDirection_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (value : Value) (inside : value.edge.Within logical.length) :
    sortDirection (relocateValue rename value) physical =
      (sortDirection value logical).map (fun pair => (pair.1, physical)) := by
  have paired := layout.truth value inside
  cases value with
  | scalar scalar => exact paired
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    cases object : logical[address] <;> simp only [object, relocateObject] at moved
    case «instance» origin name fields | dataInstance origin name frozen declared fields =>
      simp [sortDirection, found, object, moved, relocateValue, Mutable.unsupported, Mutable.eval_bind]
    all_goals simpa [sortDirection, found, object, moved, relocateValue, Mutable.unsupported, Mutable.eval_bind] using paired

theorem sortDirection_heap (heap after : Mutable.Heap) (value : Value)
    (inside : value.edge.Within heap.length) (outcome : Except ExceptionObject Bool)
    (executed : sortDirection value heap = some (outcome, after)) : after = heap := by
  have paired := sortDirection_relocates heap heap id (RuntimeLayout.refl heap) value inside
  simp only [relocateValue_id, executed, Option.map_some] at paired
  exact congrArg Prod.snd (Option.some.inj paired)

def sortListCore (address : Nat) (reverse : Bool) : Mutable.Eval Value := do
  let heap ← get
  let some (.list items) := heap[address]? | Mutable.unsupported
  if !(scalarValues items) then Mutable.unsupported
  else match HeapSort.sortWithReverse heap reverse items with
    | some (.ok sorted) =>
        set (heap.set address (.list sorted))
        pure (.scalar .none)
    | _ => Mutable.unsupported

theorem primitive_sort_core (address : Nat) : primitive (.sort address) [] = sortListCore address false := by
  funext heap
  simp [primitive, sortListCore, scalarValues_all, HeapSort.sortWithReverse]
  rfl

theorem primitive_sortReverse_core (address : Nat) (reverse : Value) :
    primitive (.sortReverse address) [reverse] = (sortDirection reverse >>= sortListCore address) := by
  funext heap
  cases reverse with
  | scalar scalar => simp [primitive, sortDirection, sortListCore, scalarValues_all, Mutable.eval_bind] <;> rfl
  | ref position =>
    cases found : heap[position]? with
    | none => simp [primitive, sortDirection, sortListCore, scalarValues_all, found, Mutable.eval_bind] <;> rfl
    | some object => cases object <;> simp [primitive, sortDirection, sortListCore, scalarValues_all, found, Mutable.eval_bind, Mutable.unsupported] <;> rfl

theorem sortListCore_scalars (heap : Mutable.Heap) (address : Nat) (reverse : Bool) (items : List Constant)
    (found : heap[address]? = some (.list (items.map Mutable.Value.scalar))) :
    sortListCore address reverse heap = match sortedScalars reverse items with
      | .error _ => none
      | .ok sorted => some (.ok (.scalar .none), heap.set address (.list (sorted.map Mutable.Value.scalar))) := by
  have scalarOnly : scalarValues (items.map Mutable.Value.scalar) = true := by
    clear found
    induction items with
    | nil => rfl
    | cons item items ih => exact ih
  simp [sortListCore, found, scalarOnly, sortWithReverse_scalars]
  cases sortedScalars reverse items <;> rfl

end FormalSW.PyAst.HeapCalls.Relocation
