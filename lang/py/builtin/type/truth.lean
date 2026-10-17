import lang.py.builtin.type.core

/-! Python truth-value testing, including `__bool__`, `__len__`, and default truth. -/

namespace FormalSW.Py.Builtin.Truth

open FormalSW.Py.Builtin

structure TruthModel (α : Type u) where
  boolMethod : Option (α → Result Bool) := none
  lengthMethod : Option (α → Result Int) := none

def test (model : TruthModel α) (value : α) : Result Bool :=
  match model.boolMethod with
  | some boolMethod => boolMethod value
  | none =>
      match model.lengthMethod with
      | none => .ok true
      | some lengthMethod => do
          let length ← lengthMethod value
          if length < 0 then .error (.valueError "__len__() should return >= 0")
          else return length != 0

def andValue (model : TruthModel α) (left right : α) : Result α := do
  if ← test model left then return right else return left

def orValue (model : TruthModel α) (left right : α) : Result α := do
  if ← test model left then return left else return right

def notValue (model : TruthModel α) (value : α) : Result Bool := (!·) <$> test model value

end FormalSW.Py.Builtin.Truth
