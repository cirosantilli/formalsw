import lang.py.FormalSW.NumericBuiltinRelocation
import lang.py.FormalSW.ListInplaceRelocation

/-! Unkeyed extrema acquire builtin sequences before scalar validation and selection. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

/-- The primitive extrema accept scalar sets in addition to builtin sequences. -/
def extremumPool (source : Value) : Mutable.Eval (List Value) := do
  match source with
  | .ref address => match (← get)[address]? with
      | some (.set items) => pure (items.map Mutable.Value.scalar)
      | _ => Mutable.sequence source
  | _ => Mutable.sequence source

theorem extremumPool_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (source : Value) (inside : source.edge.Within logical.length) :
    extremumPool (relocateValue rename source) physical =
      (extremumPool source logical).map (fun pair => (pair.1.map (List.map (relocateValue rename)), physical)) := by
  cases source with
  | scalar scalar => exact layout.sequence (.scalar scalar) inside
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    cases object : logical[address] <;> simp only [object, relocateObject] at moved <;>
      simp [extremumPool, Mutable.sequence, relocateValue, found, object, moved,
        Except.map, List.map_map, Function.comp_def, Mutable.error, Mutable.unsupported]

theorem extremumPool_heap (heap after : Mutable.Heap) (source : Value) (inside : source.edge.Within heap.length)
    (outcome : Except ExceptionObject (List Value)) (executed : extremumPool source heap = some (outcome, after)) : after = heap := by
  have paired := extremumPool_relocates heap heap id (RuntimeLayout.refl heap) source inside
  simp only [relocateValue_id, executed, Option.map_some] at paired
  exact congrArg Prod.snd (Option.some.inj paired)

def extremumSequence (maximum : Bool) (items : List Constant) : Option (Except ExceptionObject Constant) :=
  some (if maximum then ScalarSet.maximum items else ScalarSet.minimum items)

def extremumPositional (maximum : Bool) (items : List Constant) : Option (Except ExceptionObject Constant) :=
  if maximum then Calls.positionalMaximum items else Calls.positionalMinimum items

def extremumPrimitive (maximum : Bool) : List Value → Mutable.Eval Value
  | [source] => do
      let items ← extremumPool source
      scalarArgumentCall (extremumSequence maximum) items
  | values => scalarArgumentCall (extremumPositional maximum) values

theorem primitive_extremum_eq (maximum : Bool) (values : List Value) :
    primitive (.builtin (if maximum then .max else .min)) values = extremumPrimitive maximum values := by
  cases maximum <;> funext heap
  all_goals rcases values with _ | ⟨value, _ | ⟨extra, rest⟩⟩
  all_goals try rfl
  all_goals cases value with
    | scalar scalar => rfl
    | ref address =>
      cases found : heap[address]? with
      | none => simp [primitive, extremumPrimitive, extremumPool, scalarArgumentCall, extremumSequence, found, Mutable.eval_bind] <;> rfl
      | some object => cases object <;>
          simp [primitive, extremumPrimitive, extremumPool, scalarArgumentCall, extremumSequence, found, Mutable.eval_bind] <;> rfl

end FormalSW.PyAst.HeapCalls.Relocation
