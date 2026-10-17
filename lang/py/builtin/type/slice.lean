import lang.py.builtin.type.core

/-! Python slice normalization, shared by all modeled sequence types. -/

namespace FormalSW.Py.Builtin.Slice

open FormalSW.Py.Builtin

structure Slice where
  start : Option Int := none
  stop : Option Int := none
  step : Option Int := none
deriving Repr, DecidableEq

private def clamp (value low high : Int) : Int := max low (min value high)

private def normalizePositiveBound (length : Nat) (default : Int) : Option Int → Int
  | none => default
  | some value =>
      let shifted := if value < 0 then value + length else value
      clamp shifted 0 length

private def normalizeNegativeStart (length : Nat) : Option Int → Int
  | none => (length : Int) - 1
  | some value =>
      let shifted := if value < 0 then value + length else value
      clamp shifted (-1) ((length : Int) - 1)

private def normalizeNegativeStop (length : Nat) : Option Int → Int
  | none => -1
  | some value =>
      let shifted := if value < 0 then value + length else value
      clamp shifted (-1) ((length : Int) - 1)

/-- Equivalent to Python's `slice.indices(length)`. -/
def indices (slice : Slice) (length : Nat) : Result (Int × Int × Int) :=
  let step := slice.step.getD 1
  if step = 0 then
    .error (.valueError "slice step cannot be zero")
  else if step > 0 then
    .ok (
      normalizePositiveBound length 0 slice.start,
      normalizePositiveBound length length slice.stop,
      step)
  else
    .ok (
      normalizeNegativeStart length slice.start,
      normalizeNegativeStop length slice.stop,
      step)

private def indexListFuel : Nat → Int → Int → Int → List Nat
  | 0, _, _, _ => []
  | fuel + 1, current, stop, step =>
      let within := if step > 0 then current < stop else current > stop
      if within then current.toNat :: indexListFuel fuel (current + step) stop step
      else []

/-- The concrete non-negative indices selected by a slice. -/
def indexList (slice : Slice) (length : Nat) : Result (List Nat) := do
  let (start, stop, step) ← indices slice length
  return indexListFuel length start stop step

example : indexList {} 4 = .ok [0, 1, 2, 3] := rfl
example : indexList { step := some (-1) } 4 = .ok [3, 2, 1, 0] := rfl

end FormalSW.Py.Builtin.Slice
