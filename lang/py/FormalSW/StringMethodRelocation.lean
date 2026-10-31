import lang.py.FormalSW.PositionalRelocation

/-! Joining reads a builtin sequence without copying or changing its elements. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

def joinPart : Value → Mutable.Eval String
  | .scalar (.string text) => pure text
  | _ => Mutable.error "TypeError"

def stringValue : Value → Except ExceptionObject String
  | .scalar (.string text) => .ok text
  | _ => .error ⟨"TypeError", []⟩

def stringValues : List Value → Except ExceptionObject (List String)
  | [] => .ok []
  | first :: rest => match stringValue first with
      | .error exception => .error exception
      | .ok text => (stringValues rest).map (text :: ·)

theorem joinPart_eval (heap : Mutable.Heap) (value : Value) :
    joinPart value heap = some (stringValue value, heap) := by
  cases value with
  | ref address => rfl
  | scalar scalar => cases scalar <;> rfl

theorem stringValues_eval (heap : Mutable.Heap) (items : List Value) :
    items.mapM joinPart heap = some (stringValues items, heap) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    cases converted : stringValue first <;> cases remaining : stringValues rest <;>
      simp [List.mapM_cons, Mutable.eval_bind, joinPart_eval, converted, remaining, ih, stringValues, Except.map]

theorem stringValues_relocates (rename : Nat → Nat) (items : List Value) :
    stringValues (items.map (relocateValue rename)) = stringValues items := by
  have same (value : Value) : stringValue (relocateValue rename value) = stringValue value := by cases value <;> rfl
  induction items with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons, stringValues, same, ih]

def joinValues (separator : String) (items : List Value) : Mutable.Eval Value :=
  (fun strings => .scalar (.string (String.intercalate separator strings))) <$> items.mapM joinPart

theorem joinValues_scalar (separator : String) (items : List Value) :
    joinValues separator items = scalarResult (some ((stringValues items).map fun strings => .string (String.intercalate separator strings))) := by
  funext heap
  simp only [joinValues, Mutable.eval_map, stringValues_eval]
  cases stringValues items <;> rfl

theorem primitive_join_pool (separator : String) (value : Value) :
    primitive (.join separator) [value] = (positionalPool value >>= joinValues separator) := by
  funext heap
  cases value with
  | scalar scalar => simp [primitive, positionalPool, joinValues, Mutable.eval_bind] <;> rfl
  | ref address =>
    cases found : heap[address]? with
    | none => simp [primitive, positionalPool, joinValues, found, Mutable.eval_bind] <;> rfl
    | some object => cases object <;> simp [primitive, positionalPool, joinValues, found, Mutable.eval_bind, Mutable.unsupported] <;> rfl

def stringIndexFailure (address : Nat) : Mutable.Eval Value := do
  match (← get)[address]? with
  | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) | none => Mutable.unsupported
  | _ => Mutable.error "TypeError"

theorem primitive_zfill_ref (text : String) (address : Nat) :
    primitive (.zfill text) [.ref address] = stringIndexFailure address := rfl

theorem primitive_replace_ref (heap : Mutable.Heap) (text old new : String) (address : Nat) (object : Mutable.Object)
    (found : heap[address]? = some object) :
    primitive (.replace text) [.scalar (.string old), .scalar (.string new), .ref address] heap =
      stringIndexFailure address heap := by
  cases object <;> simp [primitive, stringIndexFailure, found]

end FormalSW.PyAst.HeapCalls.Relocation
