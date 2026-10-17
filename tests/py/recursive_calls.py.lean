import «.formalsw».tests.py.«recursive_calls.py.ast»
import FormalSW

namespace tests.py.recursive_calls
open FormalSW.PyAst FormalSW.PyAst.Calls

private theorem countdown_result (n : Nat) :
    ReturnsValue RecursiveCallsAst.module "countdown" [.int n] (.int n) := by
  induction n with
  | zero =>
      apply BlockReturns.function rfl rfl
      apply BlockReturns.branch (value := .bool true)
      · exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant rfl
      · exact BlockReturns.return_value Evaluates.constant
  | succ n ih =>
      apply BlockReturns.function rfl rfl
      apply BlockReturns.branch (value := .bool false)
      · apply Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
        simp [scalarCompare, evalCmpOp]
        omega
      · apply BlockReturns.return_value
        apply Evaluates.binary (av := .int n) (bv := .int 1)
        · apply Evaluates.call (values := [.int n]) _ ih
          exact .cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant
            (by simp [scalarBinary])) .nil
        · exact Evaluates.constant
        · simp [scalarBinary]

theorem countdown.returns (n : Nat) :
    (Calls.function RecursiveCallsAst.module "countdown" [.int n]).Returns :=
  (countdown_result n).returns

private theorem delegated_result (n : Nat) :
    ReturnsValue RecursiveCallsAst.module "delegated" [.int n] (.int n) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (countdown_result n)

theorem delegated.equiv (n : Nat) :
    (Calls.function RecursiveCallsAst.module "delegated" [.int n]).Equiv
      (Calls.function RecursiveCallsAst.module "countdown" [.int n]) :=
  (delegated_result n).equiv (countdown_result n)

private theorem choose_result (n : Int) :
    ReturnsValue RecursiveCallsAst.module "choose" [.int n] (.int 7) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.conditional (c := .bool true)
  · by_cases h : n = 0
    · apply Evaluates.boolean_stop (value := .bool true)
      · exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
          (by simp [scalarCompare, evalCmpOp, h])
      · rfl
    · apply Evaluates.boolean_continue (first := .bool false)
      · exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
          (by simp [scalarCompare, evalCmpOp, h])
      · rfl
      · exact Evaluates.boolean_last Evaluates.constant
  · exact Evaluates.constant

theorem choose.«Returns» (n : Int) :
    (Calls.function RecursiveCallsAst.module "choose" [.int n]).Returns :=
  (choose_result n).returns

private theorem subtract_result (a b : Int) :
    ReturnsValue RecursiveCallsAst.module "subtract" [.int a, .int b] (.int (a-b)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl)
    (by simp [scalarBinary])

private theorem nested_result (n : Int) :
    ReturnsValue RecursiveCallsAst.module "nested" [.int n] (.int n) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.call (values := [.int (n-1), .int (2-3)])
  · exact .cons (Evaluates.call
      (.cons (Evaluates.lookup rfl) (.cons Evaluates.constant .nil)) (subtract_result n 1))
      (.cons (Evaluates.call (.cons Evaluates.constant (.cons Evaluates.constant .nil))
        (subtract_result 2 3)) .nil)
  · simpa using subtract_result (n-1) (2-3)

theorem nested.«Returns» (n : Int) :
    (Calls.function RecursiveCallsAst.module "nested" [.int n]).Returns :=
  (nested_result n).returns

end tests.py.recursive_calls
