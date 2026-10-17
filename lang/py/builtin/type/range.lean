import lang.py.builtin.type.core
import lang.py.builtin.type.sequence

/-! Constant-space semantics for Python's immutable integer `range`. -/

namespace FormalSW.Py.Builtin.Range

open FormalSW.Py.Builtin

structure Range where
  start : Int
  stop : Int
  step : Int
deriving Repr, DecidableEq

def create (start stop : Int) (step : Int := 1) : Result Range :=
  if step = 0 then .error (.valueError "range() arg 3 must not be zero")
  else .ok ⟨start, stop, step⟩

def fromStop (stop : Int) : Range := ⟨0, stop, 1⟩

def length (range : Range) : Nat :=
  if range.step > 0 then
    if range.start ≥ range.stop then 0
    else ((range.stop - range.start - 1) / range.step + 1).toNat
  else
    if range.start ≤ range.stop then 0
    else ((range.start - range.stop - 1) / (-range.step) + 1).toNat

def get? (range : Range) (index : Int) : Option Int := do
  let normalized ← Sequence.normalizeIndex (length range) index
  return range.start + range.step * normalized

def contains (range : Range) (value : Int) : Bool :=
  let within :=
    if range.step > 0 then range.start ≤ value && value < range.stop
    else range.stop < value && value ≤ range.start
  within && Int.emod (value - range.start) range.step = 0

def index? (range : Range) (value : Int) : Option Nat :=
  if contains range value then some ((value - range.start) / range.step).toNat else none

private def toListFuel : Nat → Int → Int → List Int
  | 0, _, _ => []
  | count + 1, current, step => current :: toListFuel count (current + step) step

def toList (range : Range) : List Int := toListFuel (length range) range.start range.step
def count (range : Range) (value : Int) : Nat := if contains range value then 1 else 0

/-- Range equality is sequence equality, not constructor-field equality. -/
def equivalent (left right : Range) : Bool :=
  let leftLength := length left
  let rightLength := length right
  leftLength = rightLength &&
    (leftLength = 0 ||
      (left.start = right.start && (leftLength = 1 || left.step = right.step)))

example : toList (fromStop 4) = [0, 1, 2, 3] := rfl
example : toList (⟨3, -1, -1⟩ : Range) = [3, 2, 1, 0] := rfl
example : equivalent ⟨0, 0, 1⟩ ⟨2, 1, 3⟩ = true := rfl

end FormalSW.Py.Builtin.Range
