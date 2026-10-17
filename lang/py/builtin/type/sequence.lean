import lang.py.builtin.type.slice

/-! Operations shared by Python list, tuple, range, text, and binary sequences. -/

namespace FormalSW.Py.Builtin.Sequence

open FormalSW.Py.Builtin
open FormalSW.Py.Builtin.Slice

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

private theorem get_range (values : List α) :
    (List.range values.length).filterMap (fun index => values[index]?) = values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simpa [List.range_succ_eq_map, List.filterMap_map, Function.comp_def] using
        congrArg (List.cons value) ih

/-- A full negative-unit slice reverses any sequence of values. -/
theorem slice_reverse (values : List α) :
    slice values { step := some (-1) } = .ok values.reverse := by
  unfold slice
  rw [Slice.indexList_reverse]
  change Except.ok ((List.range values.length).reverse.filterMap (fun index => values[index]?)) = _
  rw [List.filterMap_reverse, get_range]

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

end FormalSW.Py.Builtin.Sequence
