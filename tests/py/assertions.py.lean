import «.formalsw».tests.py.«assertions.py.ast»
import FormalSW

namespace tests.py.assertions
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := AssertionsAst.module

theorem guarded.result (n : Int) (positive : n ≥ 1) :
    ReturnsValue program "guarded" [.int n] (.int n) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assertion (value := .bool true)
  · apply Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
    simp [scalarCompare, evalCmpOp, positive]
  · rfl
  · exact BlockReturns.return_value (Evaluates.lookup rfl)

theorem guarded.«Returns» (n : Int) (hp : Calls.Condition program
      (fun key => if key = "n" then some (.int n) else none) AssertionsAst.requires_guarded_0) :
    (function program "guarded" [.int n]).Returns := by
  have hn : n ≥ 1 := by
    simpa [evalCmpOp] using Evaluates.condition_int_compare hp rfl
  exact (guarded.result n hn).returns

theorem heap_guarded.«Returns» (n : Int) :
    (HeapCalls.scalarFunction program "heap_guarded" [.int n]).Returns := by
  exact ⟨.int n, Execution.finishes_of_observe (fuel := 40) rfl⟩

theorem heap_guarded.«Supported» (n : Int) :
    (HeapCalls.scalarFunction program "heap_guarded" [.int n]).Supported :=
  (heap_guarded.«Returns» n).supported

theorem failed.throws (n : Int) : (function program "failed" [.int n]).Throws := by
  exact ⟨⟨"AssertionError", [.int n]⟩, Execution.finishes_of_observe (fuel := 20) rfl⟩

end tests.py.assertions
