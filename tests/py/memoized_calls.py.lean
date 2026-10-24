import «.formalsw».tests.py.«memoized_calls.py.ast»
import FormalSW
import lang.py.FormalSW.MemoCallRules

namespace tests.py.memoized_calls
open FormalSW.PyAst FormalSW.PyAst.MemoCalls

private abbrev program := MemoizedCallsAst.module

private def spec (key : Key) (value : Constant) : Prop :=
  ∃ n : Nat, key = ⟨"count", [n]⟩ ∧ value = .int n

private theorem count_body (n : Nat) :
    ReturnsValue program ["count"] spec "count" [.int n] (.int n) := by
  induction n with
  | zero =>
      apply BlockReturns.memoized_function (values := [0]) (by simp) rfl rfl
      · apply BlockReturns.branch (value := .bool true)
        · exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant rfl
        · exact BlockReturns.return_value Evaluates.constant
      · exact ⟨0, rfl, rfl⟩
      · rintro other ⟨k, same, rfl⟩
        have equalInt : (0 : Int) = k := by simpa [Key.mk.injEq] using same
        have zero : k = 0 := by omega
        simp [zero]
  | succ n ih =>
      apply BlockReturns.memoized_function (values := [n + 1]) (by simp) rfl rfl
      · apply BlockReturns.branch (value := .bool false)
        · apply Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
          simp [scalarCompare, evalCmpOp]
        · apply BlockReturns.return_value
          apply Evaluates.binary (av := .int 1) (bv := .int n)
          · exact Evaluates.constant
          · apply Evaluates.call (values := [.int n])
            · exact .cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant
                (by simp [scalarBinary])) .nil
            · exact ih
          · simp [scalarBinary, Int.add_comm]
      · exact ⟨n + 1, rfl, rfl⟩
      · rintro other ⟨k, same, rfl⟩
        have equalInt : (k : Int) = n + 1 := by simpa [Key.mk.injEq, eq_comm] using same
        have equal : k = n + 1 := by omega
        simp [equal]

theorem count.«Returns» (n : Int) (hp : Calls.Condition program
    (fun key => if key = "n" then some (.int n) else none) MemoizedCallsAst.requires_count_0) :
    (sourceFunction program "count" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare hp rfl
  simpa [sourceFunction, Int.toNat_of_nonneg nonnegative] using (count_body n.toNat).returns

theorem count.«Supported» (n : Int) (hp : Calls.Condition program
    (fun key => if key = "n" then some (.int n) else none) MemoizedCallsAst.requires_count_0) :
    (sourceFunction program "count" [.int n]).Supported := (count.«Returns» n hp).supported

private theorem twice_body (n : Nat) :
    ReturnsValue program ["count"] spec "twice" [.int n] (.int (n + n)) := by
  apply BlockReturns.function (by simp) rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary (av := .int n) (bv := .int n)
  · exact Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (count_body n)
  · exact Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (count_body n)
  · simp [scalarBinary]

theorem twice.«Returns» (n : Int) (hp : Calls.Condition program
    (fun key => if key = "n" then some (.int n) else none) MemoizedCallsAst.requires_twice_0) :
    (sourceFunction program "twice" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare hp rfl
  simpa [sourceFunction, Int.toNat_of_nonneg nonnegative] using (twice_body n.toNat).returns

theorem twice.«Supported» (n : Int) (hp : Calls.Condition program
    (fun key => if key = "n" then some (.int n) else none) MemoizedCallsAst.requires_twice_0) :
    (sourceFunction program "twice" [.int n]).Supported := (twice.«Returns» n hp).supported

theorem guarded.«Returns» (n : Int)
    (_ : Calls.Condition program (fun key => if key = "n" then some (.int n) else none)
      MemoizedCallsAst.requires_guarded_0)
    (_ : SourceCondition program (fun key => if key = "n" then some (.int n) else none)
      MemoizedCallsAst.requires_guarded_1) :
    (scalarFunction program "guarded" [.int n]).Returns := ⟨.int n, .done rfl⟩

theorem requires_guarded_1_supported (n : Int)
    (hp : Calls.Condition program (fun key => if key = "n" then some (.int n) else none)
      MemoizedCallsAst.requires_guarded_0) :
    (sourceEvaluate program (fun key => if key = "n" then some (.int n) else none)
      MemoizedCallsAst.requires_guarded_1).Supported := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare hp rfl
  have run : Evaluates program ["count"] spec
      (fun key => if key = "n" then some (.int n) else none)
      MemoizedCallsAst.requires_guarded_1 (.bool true) := by
    apply Evaluates.compare (av := .int n) (bv := .int n)
    · apply Evaluates.call (.cons (Evaluates.lookup rfl) .nil)
      simpa [Int.toNat_of_nonneg nonnegative] using count_body n.toNat
    · exact Evaluates.lookup rfl
    · simp [scalarCompare, evalCmpOp]
  exact Execution.supported_of_finishes (run.finishes (Cache.valid_empty spec))

theorem same.«Equiv(count)» (n : Int)
    (hp : Calls.Condition program (fun key => if key = "n" then some (.int n) else none)
      MemoizedCallsAst.requires_same_0) :
    (scalarFunction program "same" [.int n]).Equiv (sourceFunction program "count" [.int n]) := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare hp rfl
  have left : Finishes (scalarFunction program "same" [.int n]).step
      (scalarFunction program "same" [.int n]).initial (.ok (.int n)) := .done rfl
  have right : Finishes (sourceFunction program "count" [.int n]).step
      (sourceFunction program "count" [.int n]).initial (.ok (.int n)) := by
    simpa [sourceFunction, function, Int.toNat_of_nonneg nonnegative] using
      (count_body n.toNat).finishes (Cache.valid_empty spec)
  intro outcome
  constructor
  · intro finished
    rw [finished.unique left]
    exact right
  · intro finished
    rw [finished.unique right]
    exact left

theorem same.«Supported» :
    (∀ n : Int, Calls.Condition program (fun key => if key = "n" then some (.int n) else none)
      MemoizedCallsAst.requires_same_0 → (scalarFunction program "same" [.int n]).Supported) ∧
    (∀ n : Int, Calls.Condition program (fun key => if key = "n" then some (.int n) else none)
      MemoizedCallsAst.requires_same_0 → (sourceFunction program "count" [.int n]).Supported) := by
  constructor
  · intro n _
    exact Execution.Returns.supported ⟨.int n, .done rfl⟩
  · intro n hp
    have nonnegative : 0 ≤ n := by
      simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare hp rfl
    simpa [sourceFunction, Int.toNat_of_nonneg nonnegative] using (count_body n.toNat).returns.supported

end tests.py.memoized_calls
