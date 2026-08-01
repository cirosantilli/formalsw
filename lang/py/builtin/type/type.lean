import lang.py.builtin.type.dict
import lang.py.builtin.type.object

/-! Python type objects and nominal subclass traversal. -/

namespace CleanXY.Py.Builtin.Type

open CleanXY.Py.Builtin

structure TypeObject where
  identity : Nat
  name : String
  qualname : String
  moduleName : String
  doc : Option String := none
  typeParameters : List String := []
  bases : List Nat := []
deriving Repr, DecidableEq

/-- Type registries use the same balanced-tree dictionary model as Python mappings. -/
abbrev Registry := Dict.Dict Nat TypeObject

def emptyRegistry : Registry := Dict.empty
def register (registry : Registry) (typeObject : TypeObject) : Registry :=
  Dict.set registry typeObject.identity typeObject
def find? (registry : Registry) (identity : Nat) : Option TypeObject := Dict.get? registry identity

private def isSubclassFuel (registry : Registry) (target : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, candidate =>
      if candidate = target then true
      else
        match find? registry candidate with
        | none => false
        | some typeObject => typeObject.bases.any (isSubclassFuel registry target fuel)

def isSubclass (registry : Registry) (candidate target : Nat) : Bool :=
  isSubclassFuel registry target (Dict.size registry + 1) candidate

def isInstance (registry : Registry) (object : Object.Object α) (target : Nat) : Bool :=
  isSubclass registry object.typeId target

/-- One-argument `type(object)` returns the registered runtime type. -/
def typeOf? (registry : Registry) (object : Object.Object α) : Option TypeObject :=
  find? registry object.typeId

/-- Three-argument `type(name, bases, namespace)` creates a new nominal type object. -/
def create (identity : Nat) (name moduleName : String) (bases : List Nat)
    (doc : Option String := none) : TypeObject :=
  { identity, name, qualname := name, moduleName, bases, doc }

end CleanXY.Py.Builtin.Type
