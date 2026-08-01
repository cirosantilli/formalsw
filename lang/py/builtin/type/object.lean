import lang.py.builtin.type.core

/-! Python object identity, instance attributes, callability, and hashing contracts. -/

namespace CleanXY.Py.Builtin.Object

open CleanXY.Py.Builtin

/-- An object whose attribute values are represented by `α`. -/
structure Object (α : Type u) where
  identity : Nat
  typeId : Nat
  attributes : List (String × α) := []
  callable : Bool := false
deriving Repr

def create (identity typeId : Nat) : Object α := { identity, typeId }

private def lookupAttribute : List (String × α) → String → Option α
  | [], _ => none
  | (key, value) :: rest, name => if key = name then some value else lookupAttribute rest name

def getAttr? (object : Object α) (name : String) : Option α :=
  lookupAttribute object.attributes name

def hasAttr (object : Object α) (name : String) : Bool := (getAttr? object name).isSome

private def setAttribute : List (String × α) → String → α → List (String × α)
  | [], name, value => [(name, value)]
  | (key, old) :: rest, name, value =>
      if key = name then (key, value) :: rest else (key, old) :: setAttribute rest name value

def setAttr (object : Object α) (name : String) (value : α) : Object α :=
  { object with attributes := setAttribute object.attributes name value }

def delAttr (object : Object α) (name : String) : Result (Object α) :=
  if hasAttr object name then
    .ok { object with attributes := object.attributes.filter fun entry => entry.1 != name }
  else .error (.attributeError s!"object has no attribute '{name}'")

def vars (object : Object α) : List (String × α) := object.attributes
def dir (object : Object α) : List String := object.attributes.map Prod.fst |>.mergeSort
def id (object : Object α) : Nat := object.identity
def isCallable (object : Object α) : Bool := object.callable

/-- A hash implementation together with Python's required equality consistency. -/
structure HashModel (α : Type u) where
  hash : α → Int
  equal : α → α → Bool
  equal_hash : ∀ left right, equal left right = true → hash left = hash right

end CleanXY.Py.Builtin.Object
