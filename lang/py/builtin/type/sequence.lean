import lang.py.builtin.type.slice

/-! Operations shared by Python list, tuple, range, text, and binary sequences. -/

namespace CleanXY.Py.Builtin.Sequence

open CleanXY.Py.Builtin
open CleanXY.Py.Builtin.Slice

/-- Convert a Python index to a non-negative index relative to a sequence length. -/
def normalizeIndex (length : Nat) (index : Int) : Option Nat :=
  let shifted := if index < 0 then index + length else index
  if shifted < 0 || shifted ≥ length then none else some shifted.toNat

def get? (values : List α) (index : Int) : Option α := do
  let normalized ← normalizeIndex values.length index
  values[normalized]?

def get (values : List α) (index : Int) : Result α :=
  match get? values index with
  | some value => .ok value
  | none => .error (.indexError "sequence index out of range")

def slice (values : List α) (bounds : Slice) : Result (List α) := do
  let indices ← Slice.indexList bounds values.length
  return indices.filterMap fun index => values[index]?

def contains [BEq α] (values : List α) (needle : α) : Bool := values.contains needle
def concat (left right : List α) : List α := left ++ right
def repeated (values : List α) (count : Int) : List α :=
  List.replicate count.toNat values |>.flatten
def count [BEq α] (values : List α) (needle : α) : Nat :=
  values.foldl (fun total value => if value == needle then total + 1 else total) 0

private def indexFrom [BEq α] : List α → α → Nat → Option Nat
  | [], _, _ => none
  | value :: rest, needle, index =>
      if value == needle then some index else indexFrom rest needle (index + 1)

def index? [BEq α] (values : List α) (needle : α) (start : Int := 0)
    (stop : Option Int := none) : Option Nat :=
  let bounds : Slice := { start := some start, stop := stop }
  match slice values bounds with
  | .error _ => none
  | .ok selected =>
      let normalizedStart := normalizeIndex (values.length + 1) start |>.getD 0
      indexFrom selected needle normalizedStart

def lexicographicCompare (compareElement : α → α → Ordering) : List α → List α → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | left :: leftRest, right :: rightRest =>
      match compareElement left right with
      | .eq => lexicographicCompare compareElement leftRest rightRest
      | order => order

end CleanXY.Py.Builtin.Sequence
