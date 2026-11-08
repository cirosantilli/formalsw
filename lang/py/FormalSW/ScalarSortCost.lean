import lang.py.FormalSW.ScalarSort

/-! Comparison counts for the existing scalar insertion-sort implementation.
Each constructor follows one recursive clause of `ScalarSort.insert` or `sort`;
the soundness theorems recover those functions' actual results. -/
namespace FormalSW.PyAst.ScalarSort.Cost

attribute [local simp] bind pure Functor.map Except.bind Except.map Except.pure

inductive Inserts (value : Constant) : List Constant → Nat → List Constant → Prop where
  | nil : Inserts value [] 0 [value]
  | before (comparison : scalarCompare .lt first value = some false) :
      Inserts value (first :: rest) 1 (value :: first :: rest)
  | after (comparison : scalarCompare .lt first value = some true)
      (tail : Inserts value rest cost output) :
      Inserts value (first :: rest) (cost + 1) (first :: output)

namespace Inserts

theorem result (h : Inserts value input cost output) : insert value input = .ok output := by
  induction h with
  | nil => rfl
  | before comparison => simp [insert, comparison]
  | after comparison _ ih => simp [insert, comparison, ih]

theorem length (h : Inserts value input cost output) : output.length = input.length + 1 := by
  induction h with
  | nil => rfl
  | before _ => simp
  | after _ _ ih => simp [ih]

theorem bound (h : Inserts value input cost output) : cost ≤ input.length := by
  induction h with
  | nil => omega
  | before _ => simp
  | after _ _ ih => simpa using Nat.succ_le_succ ih

end Inserts

inductive Sorts : List Constant → Nat → List Constant → Prop where
  | nil : Sorts [] 0 []
  | cons (tail : Sorts rest tailCost middle) (head : Inserts first middle headCost output) :
      Sorts (first :: rest) (tailCost + headCost) output

namespace Sorts

theorem result (h : Sorts input cost output) : sort input = .ok output := by
  induction h with
  | nil => rfl
  | cons _ head ih => simp [sort, ih, head.result]

theorem length (h : Sorts input cost output) : output.length = input.length := by
  induction h with
  | nil => rfl
  | cons _ head ih => simp [head.length, ih]

/-- Twice the comparisons are bounded by n(n-1); there is no assumption that
an arbitrary `sorted` call takes constant time. -/
theorem bound (h : Sorts input cost output) : 2 * cost ≤ input.length * (input.length - 1) := by
  induction h with
  | nil => simp
  | @cons rest tailCost middle first headCost output tail head ih =>
      have inserted := head.bound
      rw [tail.length] at inserted
      have identity : (rest.length + 1) * rest.length =
          rest.length * (rest.length - 1) + 2 * rest.length := by
        cases rest.length with
        | zero => rfl
        | succ n => simp [Nat.mul_add, Nat.add_mul]; omega
      simp only [List.length_cons, Nat.add_sub_cancel]
      rw [identity, Nat.mul_add]
      omega

end Sorts

/-- Euler 9's `sorted((a,b,c))`: at most three scalar comparisons, including
the comparison against the largest final element. -/
theorem three_top (a b c : Int) (ac : a ≤ c) (bc : b ≤ c) :
    ∃ comparisons, comparisons ≤ 3 ∧ Sorts [.int a, .int b, .int c] comparisons
      [.int (min a b), .int (max a b), .int c] := by
  have last : Sorts [.int c] 0 [.int c] := .cons .nil .nil
  have middle : Sorts [.int b, .int c] 1 [.int b, .int c] :=
    .cons last (.before (by simp [scalarCompare, evalCmpOp]; omega))
  by_cases ab : a ≤ b
  · refine ⟨2, by omega, ?_⟩
    simp only [Int.min_def, Int.max_def, if_pos ab]
    exact .cons middle (.before (by simp [scalarCompare, evalCmpOp]; omega))
  · refine ⟨3, by omega, ?_⟩
    simp only [Int.min_def, Int.max_def, if_neg ab]
    exact .cons middle (.after (by simp [scalarCompare, evalCmpOp]; omega)
      (.before (by simp [scalarCompare, evalCmpOp]; omega)))

end FormalSW.PyAst.ScalarSort.Cost
