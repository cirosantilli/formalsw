import «.formalsw».tests.py.«heap_calls.py.ast»
import FormalSW

namespace tests.py.heap_calls
open FormalSW.PyAst
private abbrev program := HeapCallsAst.module

private theorem make.result (n : Int) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "make" [.scalar (.int n)] heap (.ref heap.length)
      (heap ++ [[.scalar (.int n)]]) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  exact HeapCalls.Evaluates.list (.cons (HeapCalls.Evaluates.lookup rfl) .nil)

theorem make.«Returns» (n : Int) :
    (HeapCalls.call program "make" [.scalar (.int n)] []).Returns :=
  (make.result n []).returns

theorem make.«Supported» (n : Int) :
    (HeapCalls.call program "make" [.scalar (.int n)] []).Supported :=
  (make.«Returns» n).supported

/-- The returned object is the caller's original object, for any caller heap. -/
theorem push.result (heap : Mutable.Heap) (address : Nat) (items : List Mutable.Value)
    (found : heap[address]? = some items) (value : Int) :
    HeapCalls.ReturnsValue program "push" [.ref address, .scalar (.int value)] heap (.ref address)
      (heap.set address (items ++ [.scalar (.int value)])) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.discard
  · exact HeapCalls.Evaluates.append (HeapCalls.Evaluates.lookup rfl) found
      (HeapCalls.Evaluates.lookup rfl) found
  · exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup rfl)

private theorem total.run (n : Int) : Finishes (HeapCalls.scalarFunction program "total" [.int n]).step
    (HeapCalls.scalarFunction program "total" [.int n]).initial (.ok (.int (n + 10 + n))) :=
  Execution.finishes_of_observe (fuel := 100) rfl

private theorem reference.run (n : Int) : Finishes (scalarFunction program "reference" [.int n]).step
    (scalarFunction program "reference" [.int n]).initial (.ok (.int (n + 10 + n))) :=
  Execution.finishes_of_observe (fuel := 5) rfl

theorem total.«Equiv(reference)» (n : Int) :
    (HeapCalls.scalarFunction program "total" [.int n]).Equiv (scalarFunction program "reference" [.int n]) := by
  intro outcome
  constructor
  · intro run
    rw [run.unique (total.run n)]
    exact reference.run n
  · intro run
    rw [run.unique (reference.run n)]
    exact total.run n

theorem total.«Supported» :
    (∀ n : Int, (HeapCalls.scalarFunction program "total" [.int n]).Supported) ∧
    (∀ n : Int, (scalarFunction program "reference" [.int n]).Supported) :=
  ⟨fun n => Execution.supported_of_finishes (total.run n),
   fun n => Execution.supported_of_finishes (reference.run n)⟩

end tests.py.heap_calls
