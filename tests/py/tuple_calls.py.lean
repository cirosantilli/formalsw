import «.formalsw».tests.py.«tuple_calls.py.ast»
import FormalSW

namespace tests.py.tuple_calls
open FormalSW.PyAst
private abbrev program := TupleCallsAst.module

private theorem reference.result (n : Int) :
    Finishes (scalarFunction program "reference" [.int n]).step
      (scalarFunction program "reference" [.int n]).initial (.ok (.int 1)) :=
  Execution.finishes_of_observe (fuel := 2) rfl

theorem reference.«Returns» (n : Int) :
    (scalarFunction program "reference" [.int n]).Returns :=
  ⟨_, reference.result n⟩

private theorem difference.result (n : Int) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "difference" [.scalar (.int n)] heap (.scalar (.int 1))
      (heap ++ [.tuple [.scalar (.int n), .scalar (.int (n + 1))]]) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.assign
  · exact HeapCalls.Evaluates.tuple
      (.cons (HeapCalls.Evaluates.lookup rfl) (.cons
        (HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup rfl) HeapCalls.Evaluates.constant rfl) .nil))
      (by simp)
  · apply HeapCalls.BlockReturns.unpack
      (items := [.scalar (.int n), .scalar (.int (n + 1))])
      (afterUnpack := heap ++ [.tuple [.scalar (.int n), .scalar (.int (n + 1))]])
      rfl (HeapCalls.Evaluates.lookup rfl)
    · simp [Mutable.sequence]
    · rfl
    · apply HeapCalls.BlockReturns.return_value
      exact HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup rfl) (HeapCalls.Evaluates.lookup rfl)
        (by simp [Mutable.binary, scalarBinary]; omega)

theorem difference.«Returns» (n : Int) :
    (HeapCalls.scalarFunction program "difference" [.int n]).Returns :=
  (difference.result n []).scalar_returns

theorem difference.«Equiv(reference)» (n : Int) :
    (HeapCalls.scalarFunction program "difference" [.int n]).Equiv
      (scalarFunction program "reference" [.int n]) := by
  intro outcome
  constructor
  · intro run
    rw [run.unique (difference.result n []).scalar_finishes]
    exact reference.result n
  · intro run
    rw [run.unique (reference.result n)]
    exact (difference.result n []).scalar_finishes

theorem difference.«Supported» :
    (∀ n : Int, (HeapCalls.scalarFunction program "difference" [.int n]).Supported) ∧
    (∀ n : Int, (scalarFunction program "reference" [.int n]).Supported) :=
  ⟨fun n => (difference.«Returns» n).supported,
    fun n => Execution.supported_of_finishes (reference.result n)⟩

end tests.py.tuple_calls
