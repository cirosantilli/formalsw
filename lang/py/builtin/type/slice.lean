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

private theorem reverse_indices (length : Nat) :
    indexListFuel length ((length : Int) - 1) (-1) (-1) = (List.range length).reverse := by
  induction length with
  | zero => rfl
  | succ length ih =>
      have position : ((length + 1 : Nat) : Int) - 1 = length := by omega
      have within : (-1 : Int) < length := by omega
      simpa [indexListFuel, position, within, List.range_succ, List.reverse_append] using
        congrArg (List.cons length) ih

/-- A full negative-unit slice visits each index once in reverse order. -/
theorem indexList_reverse (length : Nat) :
    indexList { step := some (-1) } length = .ok (List.range length).reverse := by
  change (.ok (indexListFuel length ((length : Int) - 1) (-1) (-1)) : Result (List Nat)) = _
  exact congrArg (Except.ok (ε := Error)) (reverse_indices length)

example : indexList {} 4 = .ok [0, 1, 2, 3] := rfl
example : indexList { step := some (-1) } 4 = .ok [3, 2, 1, 0] := rfl

private theorem count_next (start stop stride : Nat) (positive : 0 < stride) (within : start < stop) :
    (stop - start + stride - 1) / stride =
      (stop - (start + stride) + stride - 1) / stride + 1 := by
  have rearrange : stop - start + stride - 1 = (stop - start - 1) + stride := by omega
  rw [rearrange, Nat.add_div_right _ positive]
  by_cases near : stop ≤ start + stride
  · have zero : stop - (start + stride) = 0 := by omega
    have small : stop - start - 1 < stride := by omega
    simp [zero, Nat.div_eq_of_lt small, Nat.div_eq_of_lt (show stride - 1 < stride by omega)]
  · congr 1
    congr 1
    omega

private theorem indexListFuel_positive (fuel start stop stride : Nat)
    (positive : 0 < stride) (enough : stop ≤ start + fuel) :
    indexListFuel fuel start stop stride =
      List.range' start ((stop - start + stride - 1) / stride) stride := by
  induction fuel generalizing start with
  | zero =>
      have empty : stop - start = 0 := by omega
      simp [indexListFuel, empty, Nat.div_eq_of_lt (show stride - 1 < stride by omega)]
  | succ fuel ih =>
      have stridePositive : (0 : Int) < stride := by omega
      by_cases within : start < stop
      · have withinInt : (start : Int) < stop := by omega
        rw [indexListFuel]
        simp only [stridePositive, withinInt, ↓reduceIte, Int.toNat_natCast]
        rw [← Int.natCast_add, ih (start + stride) (by omega), count_next start stop stride positive within]
        rw [List.range'_succ]
      · have outside : ¬ (start : Int) < stop := by omega
        have empty : stop - start = 0 := by omega
        simp only [indexListFuel, stridePositive, outside, ↓reduceIte, empty, Nat.zero_add,
          Nat.div_eq_of_lt (show stride - 1 < stride by omega), List.range'_zero]

/-- A positive slice to the end selects an arithmetic progression. -/
private theorem indexList_positive_end_of_le (length start stride : Nat) (positive : 0 < stride)
    (within : start ≤ length) :
    indexList { start := some start, step := some stride } length =
      .ok (List.range' start ((length - start + stride - 1) / stride) stride) := by
  have stridePositive : (0 : Int) < stride := by omega
  have strideNonzero : (stride : Int) ≠ 0 := by omega
  have startNonnegative : ¬ (start : Int) < 0 := by omega
  have castWithin : (start : Int) ≤ length := by omega
  have clamped : max (0 : Int) (min (start : Int) length) = start := by omega
  simp only [indexList, indices, Option.getD_some, strideNonzero, ↓reduceIte,
    stridePositive, normalizePositiveBound, startNonnegative, clamp,
    clamped]
  change Except.ok (indexListFuel length start length stride) = _
  rw [indexListFuel_positive length start length stride positive (by omega)]

/-- Positive slices to the end remain empty when their start is beyond the sequence. -/
theorem indexList_positive_end (length start stride : Nat) (positive : 0 < stride) :
    indexList { start := some start, step := some stride } length =
      .ok (List.range' start ((length - start + stride - 1) / stride) stride) := by
  by_cases within : start ≤ length
  · exact indexList_positive_end_of_le length start stride positive within
  · have stridePositive : (0 : Int) < stride := by omega
    have strideNonzero : (stride : Int) ≠ 0 := by omega
    have startNonnegative : ¬ (start : Int) < 0 := by omega
    have clamped : max (0 : Int) (min (start : Int) length) = length := by omega
    have empty : length - start = 0 := by omega
    simp only [indexList, indices, Option.getD_some, strideNonzero, ↓reduceIte,
      stridePositive, normalizePositiveBound, startNonnegative, clamp, clamped]
    change Except.ok (indexListFuel length length length stride) = _
    rw [indexListFuel_positive length length length stride positive (by omega)]
    simp [empty, Nat.div_eq_of_lt (show stride - 1 < stride by omega)]

/-- Number of elements selected by `values[:stop]`, including negative bounds. -/
def prefixLength (length : Nat) (stop : Int) : Nat :=
  (max 0 (min (if stop < 0 then stop + length else stop) length)).toNat

theorem prefixLength_le (length : Nat) (stop : Int) : prefixLength length stop ≤ length := by
  unfold prefixLength
  omega

theorem prefixLength_nonnegative (length stop : Nat) : prefixLength length stop = min stop length := by
  unfold prefixLength
  have nonnegative : ¬ (stop : Int) < 0 := by omega
  simp only [nonnegative, ↓reduceIte]
  omega

/-- A unit-stride prefix has contiguous indices even when its bound is negative. -/
theorem indexList_prefix (length : Nat) (stop : Int) :
    indexList { stop := some stop } length = .ok (List.range (prefixLength length stop)) := by
  have normalized : (prefixLength length stop : Int) =
      max 0 (min (if stop < 0 then stop + length else stop) length) := by
    unfold prefixLength
    omega
  change Except.ok (indexListFuel length 0
    (max 0 (min (if stop < 0 then stop + length else stop) length)) 1) = _
  rw [← normalized]
  congr 1
  simpa [List.range_eq_range'] using
    indexListFuel_positive length 0 (prefixLength length stop) 1 (by decide)
      (by simpa using prefixLength_le length stop)

/-- Omitting the stride in a suffix selects every remaining position. -/
theorem indexList_suffix (length start : Nat) :
    indexList { start := some start } length = .ok (List.range' start (length - start)) := by
  simpa only [Nat.add_sub_cancel, Nat.div_one] using indexList_positive_end length start 1 (by decide)

/-- Omitting all bounds visits every index in order. -/
theorem indexList_full (length : Nat) : indexList {} length = .ok (List.range length) := by
  change Except.ok (indexListFuel length 0 length 1) = _
  congr 1
  simpa [List.range_eq_range'] using
    indexListFuel_positive length 0 length 1 (by decide) (by omega)

/-- Python's inclusive count expression matches the number of selected positions. -/
theorem positive_end_count (length start stride : Nat) (positive : 0 < stride) :
    (((length : Int) - 1 - start) / stride + 1).toNat =
      (length - start + stride - 1) / stride := by
  by_cases within : start < length
  · have rearrange : (length : Int) - 1 - start = ((length - start - 1 : Nat) : Int) := by omega
    rw [rearrange]
    change (↑((length - start - 1) / stride) + (1 : Int)).toNat = _
    change (length - start - 1) / stride + 1 = _
    have rearrangeNat : length - start + stride - 1 = (length - start - 1) + stride := by omega
    rw [rearrangeNat, Nat.add_div_right _ positive]
  · have empty : length - start = 0 := by omega
    have negative : (length : Int) - 1 - start < 0 := by omega
    have quotient := Int.ediv_neg_of_neg_of_pos negative (by omega : (0 : Int) < stride)
    rw [Int.toNat_of_nonpos (by omega), empty]
    simp [Nat.div_eq_of_lt (show stride - 1 < stride by omega)]

/-- Membership in a positive slice is a bound check and a divisibility test. -/
theorem mem_positive_end (length start stride index : Nat) (positive : 0 < stride) :
    index ∈ List.range' start ((length - start + stride - 1) / stride) stride ↔
      start ≤ index ∧ index < length ∧ stride ∣ index - start := by
  by_cases within : start < length
  · have count : (length - start + stride - 1) / stride = (length - start - 1) / stride + 1 := by
      have rearrange : length - start + stride - 1 = (length - start - 1) + stride := by omega
      rw [rearrange, Nat.add_div_right _ positive]
    have bound (k : Nat) : k < (length - start + stride - 1) / stride ↔ start + stride * k < length := by
      rw [count, Nat.lt_succ_iff, Nat.le_div_iff_mul_le positive, Nat.mul_comm k stride]
      omega
    rw [List.mem_range']
    constructor
    · rintro ⟨k, inRange, rfl⟩
      exact ⟨by omega, (bound k).mp inRange, ⟨k, by omega⟩⟩
    · rintro ⟨lower, upper, k, multiple⟩
      have equal : index = start + stride * k := by omega
      exact ⟨k, (bound k).mpr (by simpa [← equal] using upper), equal⟩
  · have empty : length - start = 0 := by omega
    simp [empty, Nat.div_eq_of_lt (show stride - 1 < stride by omega)]
    omega

end FormalSW.Py.Builtin.Slice
