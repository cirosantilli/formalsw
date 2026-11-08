import lang.py.FormalSW.HeapRuntimeInputs
import lang.py.FormalSW.HeapSortWork
import Mathlib.Data.Nat.Log

/-! String-list sizes and the existing comparison-sort tariff. The precise
tariff depends on name count and maximum character width; the total-size
envelope is conservative and does not assume bounded-length strings. -/
namespace FormalSW.PyAst.HeapCalls.Runtime.StringList
open PrimitiveWork

theorem scalar_sizes (arithmetic : Arithmetic) (values : List String) :
    ((values.map Constant.string).map (scalarSize arithmetic)).sum = size values := by
  induction values with
  | nil => rfl
  | cons text rest ih =>
      simpa only [List.map_cons, List.sum_cons, scalarSize, size_cons] using
        congrArg (fun n => text.length + 1 + n) ih

private theorem fold_max_le_sum (values : List Nat) (initial : Nat) :
    values.foldl max initial ≤ initial + values.sum := by
  induction values generalizing initial with
  | nil => simp
  | cons head rest ih =>
      have bound := ih (max initial head)
      simp only [List.foldl_cons, List.sum_cons]
      omega

theorem width_le_size (arithmetic : Arithmetic) (values : List String) :
    SetWork.width arithmetic (values.map Constant.string) ≤ size values + 1 := by
  have bound := fold_max_le_sum ((values.map Constant.string).map (scalarSize arithmetic)) 1
  simpa only [SetWork.width, scalar_sizes, Nat.add_comm] using bound

/-- Aggregate a linear character cost and fixed per-string overhead, including
empty strings, without replacing every length by the largest one. -/
theorem weighted_sum_le_size (characterCost entryCost : Nat) (values : List String) :
    (values.map (fun text => characterCost * text.length + entryCost)).sum ≤
      max characterCost entryCost * size values := by
  induction values with
  | nil => simp
  | cons text rest ih =>
      have characters := Nat.mul_le_mul_right text.length (Nat.le_max_left characterCost entryCost)
      have entry := Nat.le_max_right characterCost entryCost
      simp only [List.map_cons, List.sum_cons, size_cons, Nat.mul_add, Nat.mul_one]
      omega

/-- A total-input-size bound for the current maximum-key-width sort contract.
It deliberately retains string-comparison costs in both arithmetic models. -/
theorem sorting_bound (arithmetic : Arithmetic) (values : List String) :
    SortWork.sorting arithmetic (values.map Constant.string) ≤
      3 * (size values + 1)^2 * ((size values + 1).log2 + 1) + (size values + 1) := by
  have count : values.length + 1 ≤ size values + 1 := Nat.add_le_add_right (length_le_size values) 1
  have logarithm : (values.length + 1).log2 + 1 ≤ (size values + 1).log2 + 1 := by
    have monotone := Nat.log_mono_right (b := 2) count
    simpa only [← Nat.log2_eq_log_two] using Nat.add_le_add_right monotone 1
  have width := width_le_size arithmetic values
  have key : 2 * SetWork.width arithmetic (values.map Constant.string) + 1 ≤
      3 * (size values + 1) := by omega
  have comparisons := Nat.mul_le_mul (Nat.mul_le_mul count logarithm) key
  have budget := Nat.add_le_add comparisons count
  have rearranged : ((size values + 1) * ((size values + 1).log2 + 1)) *
      (3 * (size values + 1)) = 3 * (size values + 1)^2 * ((size values + 1).log2 + 1) := by
    simp only [Nat.pow_two]
    ac_rfl
  simpa only [SortWork.sorting, comparisonSort, sequenceCopy, List.length_map, rearranged] using budget

end FormalSW.PyAst.HeapCalls.Runtime.StringList
