import «.formalsw».tests.py.«tuple_assignments.py.ast»
import FormalSW

namespace tests.py.tuple_assignments
open FormalSW.PyAst FormalSW.PyAst.Calls

private theorem swap_result (n : Int) :
    ReturnsValue TupleAssignmentsAst.module "swap" [.int n] (.int 1) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.unpack (names := ["a", "b"]) (results := [.int n, .int (n + 1)]) rfl rfl
  · exact .cons (Evaluates.lookup rfl) (.cons
      (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary])) .nil)
  · apply BlockReturns.unpack (names := ["a", "b"]) (results := [.int (n + 1), .int n]) rfl rfl
    · exact .cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)
    · apply BlockReturns.return_value
      exact Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl)
        (by simp [scalarBinary]; omega)

theorem swap.«Returns» (n : Int) :
    (Calls.function TupleAssignmentsAst.module "swap" [.int n]).Returns :=
  (swap_result n).returns

private theorem repeated_result (n : Int) :
    ReturnsValue TupleAssignmentsAst.module "repeated" [.int n] (.int (n + 1)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.unpack (names := ["a", "a"]) (results := [.int n, .int (n + 1)]) rfl rfl
  · exact .cons (Evaluates.lookup rfl) (.cons
      (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary])) .nil)
  · exact BlockReturns.return_value (Evaluates.lookup rfl)

theorem repeated.«Returns» (n : Int) :
    (Calls.function TupleAssignmentsAst.module "repeated" [.int n]).Returns :=
  (repeated_result n).returns

private theorem empty_result (n : Int) :
    ReturnsValue TupleAssignmentsAst.module "empty" [.int n] (.int n) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.unpack (names := []) (results := []) rfl rfl .nil
  exact BlockReturns.return_value (Evaluates.lookup rfl)

theorem empty.«Returns» (n : Int) :
    (Calls.function TupleAssignmentsAst.module "empty" [.int n]).Returns :=
  (empty_result n).returns

theorem ordered.throws (n : Int) :
    (Calls.function TupleAssignmentsAst.module "ordered" [.int n]).Throws := by
  refine ⟨{ typeName := "ZeroDivisionError", args := [] }, ?_⟩
  exact Execution.finishes_of_observe (fuel := 20) rfl

end tests.py.tuple_assignments
