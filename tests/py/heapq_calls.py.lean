import «.formalsw».tests.py.«heapq_calls.py.ast»
import FormalSW

namespace tests.py.heapq_calls
open FormalSW.PyAst
private abbrev program := HeapqCallsAst.module

/-- Compose the three heap operations for every integer using their proof rules. -/
theorem solve.result (n : Int) :
    HeapCalls.ReturnsValue program "solve" [.scalar (.int n)] [] (.scalar (.int n))
      [.list []] := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.assign (HeapCalls.Evaluates.list .nil)
  apply HeapCalls.BlockReturns.discard
  · apply HeapCalls.Evaluates.builtin
      (.cons (HeapCalls.Evaluates.lookup rfl) (.cons (HeapCalls.Evaluates.lookup rfl) .nil))
    exact Heapq.heappush_empty [.list []] 0 (.scalar (.int n)) rfl
  apply HeapCalls.BlockReturns.discard
  · apply HeapCalls.Evaluates.builtin (.cons (HeapCalls.Evaluates.lookup rfl) .nil)
    exact Heapq.heapify_singleton [.list [.scalar (.int n)]] 0 (.scalar (.int n)) rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.builtin (.cons (HeapCalls.Evaluates.lookup rfl) .nil)
  exact Heapq.heappop_singleton [.list [.scalar (.int n)]] 0 (.scalar (.int n)) rfl

private theorem reference.result (n : Int) :
    Finishes (scalarFunction program "reference" [.int n]).step
      (scalarFunction program "reference" [.int n]).initial (.ok (.int n)) :=
  .done rfl

theorem solve.«Returns» (n : Int) :
    (HeapCalls.scalarFunction program "solve" [.int n]).Returns :=
  (solve.result n).scalar_returns

theorem solve.«Equiv(reference)» (n : Int) :
    (HeapCalls.scalarFunction program "solve" [.int n]).Equiv
      (scalarFunction program "reference" [.int n]) := by
  intro outcome
  constructor
  · intro run
    rw [run.unique (solve.result n).scalar_finishes]
    exact reference.result n
  · intro run
    rw [run.unique (reference.result n)]
    exact (solve.result n).scalar_finishes

theorem solve.«Supported» :
    (∀ n : Int, (HeapCalls.scalarFunction program "solve" [.int n]).Supported) ∧
      (∀ n : Int, (scalarFunction program "reference" [.int n]).Supported) :=
  ⟨fun n => (solve.«Returns» n).supported,
    fun n => Execution.supported_of_finishes (reference.result n)⟩

end tests.py.heapq_calls
