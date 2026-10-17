import lang.py.builtin.type.core

/-! Models for `property`, `classmethod`, `staticmethod`, and bound methods. -/

namespace FormalSW.Py.Builtin.Descriptor

open FormalSW.Py.Builtin

structure Property (Owner : Type u) (Value : Type v) where
  get : Option (Owner → Result Value) := none
  set : Option (Owner → Value → Result Owner) := none
  delete : Option (Owner → Result Owner) := none
  doc : Option String := none

def propertyGet (property : Property Owner Value) (owner : Owner) : Result Value :=
  match property.get with
  | some getter => getter owner
  | none => .error (.attributeError "property has no getter")

def propertySet (property : Property Owner Value) (owner : Owner) (value : Value) : Result Owner :=
  match property.set with
  | some setter => setter owner value
  | none => .error (.attributeError "property has no setter")

def propertyDelete (property : Property Owner Value) (owner : Owner) : Result Owner :=
  match property.delete with
  | some deleter => deleter owner
  | none => .error (.attributeError "property has no deleter")

def getter (property : Property Owner Value) (function : Owner → Result Value) : Property Owner Value :=
  { property with get := some function }
def setter (property : Property Owner Value) (function : Owner → Value → Result Owner) : Property Owner Value :=
  { property with set := some function }
def deleter (property : Property Owner Value) (function : Owner → Result Owner) : Property Owner Value :=
  { property with delete := some function }

structure ClassMethod (Class Args ResultType : Type) where
  function : Class → Args → ResultType

structure StaticMethod (Args ResultType : Type) where
  function : Args → ResultType

structure BoundMethod (Self Args ResultType : Type) where
  self : Self
  function : Self → Args → ResultType

def BoundMethod.call (method : BoundMethod Self Args ResultType) (args : Args) : ResultType :=
  method.function method.self args

end FormalSW.Py.Builtin.Descriptor
