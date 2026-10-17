import lang.py.builtin.type.core
import lang.py.builtin.type.type

/-! Python `super`: method-resolution search beginning after a nominated class. -/

namespace FormalSW.Py.Builtin.Super

open FormalSW.Py.Builtin

structure Super where
  nominatedType : Nat
  boundObjectType : Nat
  methodResolutionOrder : List Nat
deriving Repr, DecidableEq

private def dropThrough : List Nat → Nat → Option (List Nat)
  | [], _ => none
  | head :: tail, target => if head = target then some tail else dropThrough tail target

def create (registry : Type.Registry) (nominatedType boundObjectType : Nat)
    (methodResolutionOrder : List Nat) : Result Super :=
  if !Type.isSubclass registry boundObjectType nominatedType then
    .error (.typeError "super(type, obj): obj must be an instance or subtype of type")
  else
    match dropThrough methodResolutionOrder nominatedType with
    | none => .error (.typeError "nominated type is absent from the method resolution order")
    | some _ => .ok { nominatedType, boundObjectType, methodResolutionOrder }

/-- Resolve an attribute by consulting classes after the nominated class in MRO order. -/
def getAttr? (superObject : Super) (lookup : Nat → String → Option α)
    (name : String) : Option α := do
  let tail ← dropThrough superObject.methodResolutionOrder superObject.nominatedType
  tail.findSome? fun typeId => lookup typeId name

end FormalSW.Py.Builtin.Super
