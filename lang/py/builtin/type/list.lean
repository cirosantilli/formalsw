import lang.py.builtin.type.sequence

/-! Python's mutable list operations, modeled as pure list transformations. -/

namespace FormalSW.Py.Builtin.List

open FormalSW.Py.Builtin

abbrev ListValue (α : Type u) := List α

def empty : ListValue α := []
def ofIterable (values : List α) : ListValue α := values
def size (values : ListValue α) : Nat := values.length
def count [BEq α] (values : ListValue α) (needle : α) : Nat := Sequence.count values needle
def index [BEq α] (values : ListValue α) (needle : α) : Result Nat :=
  match Sequence.index? values needle with
  | some position => .ok position
  | none => .error (.valueError "value is not in list")
def append (values : ListValue α) (value : α) : ListValue α := values ++ [value]
def clear (_ : ListValue α) : ListValue α := []
def copy (values : ListValue α) : ListValue α := values
def extend (values additional : ListValue α) : ListValue α := values ++ additional

def insert (values : ListValue α) (index : Int) (value : α) : ListValue α :=
  let shifted := if index < 0 then index + values.length else index
  let normalized := Int.toNat (max 0 (min shifted values.length))
  values.take normalized ++ value :: values.drop normalized

def pop (values : ListValue α) (index : Int := -1) : Result (α × ListValue α) := do
  let normalized ← match Sequence.normalizeIndex values.length index with
    | some value => .ok value
    | none => .error (.indexError "pop index out of range")
  let value ← match values[normalized]? with
    | some value => .ok value
    | none => .error (.indexError "pop index out of range")
  return (value, values.take normalized ++ values.drop (normalized + 1))

def remove [BEq α] (values : ListValue α) (needle : α) : Result (ListValue α) :=
  match Sequence.index? values needle with
  | none => .error (.valueError "list.remove(x): x not in list")
  | some index => .ok (values.take index ++ values.drop (index + 1))

def reverse (values : ListValue α) : ListValue α := values.reverse

def setAt (values : ListValue α) (index : Int) (value : α) : Result (ListValue α) :=
  match Sequence.normalizeIndex values.length index with
  | none => .error (.indexError "list assignment index out of range")
  | some normalized => .ok (values.set normalized value)

def deleteAt (values : ListValue α) (index : Int) : Result (ListValue α) :=
  match Sequence.normalizeIndex values.length index with
  | none => .error (.indexError "list assignment index out of range")
  | some normalized => .ok (values.take normalized ++ values.drop (normalized + 1))

def setSlice (values : ListValue α) (bounds : Slice.Slice) (replacement : List α) :
    Result (ListValue α) := do
  let (start, stop, step) ← Slice.indices bounds values.length
  if step = 1 then
    return values.take start.toNat ++ replacement ++ values.drop stop.toNat
  else
    let indices ← Slice.indexList bounds values.length
    if indices.length != replacement.length then
      .error (.valueError "attempt to assign sequence of size mismatch to extended slice")
    else
      return (indices.zip replacement).foldl (fun result pair => result.set pair.1 pair.2) values

def deleteSlice (values : ListValue α) (bounds : Slice.Slice) : Result (ListValue α) := do
  let indices ← Slice.indexList bounds values.length
  return values.mapIdx (fun index value => (index, value))
    |>.filter (fun pair => !indices.contains pair.1)
    |>.map Prod.snd

/-- Stable insertion sort using only the supplied strict-less comparison. -/
private def insertSorted (less : α → α → Bool) (value : α) : List α → List α
  | [] => [value]
  | head :: tail =>
      if less value head then value :: head :: tail
      else head :: insertSorted less value tail

def sort (values : ListValue α) (less : α → α → Bool)
    (reverseOrder : Bool := false) : ListValue α :=
  let ordering := if reverseOrder then (fun left right => less right left) else less
  values.foldl (fun result value => insertSorted ordering value result) []

end FormalSW.Py.Builtin.List
