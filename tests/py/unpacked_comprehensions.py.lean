import «.formalsw».tests.py.«unpacked_comprehensions.py.ast»
import FormalSW

namespace tests.py.unpacked_comprehensions
open FormalSW.PyAst
private abbrev program := UnpackedComprehensionsAst.module

private theorem pair_sum.result (n : Int) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "pair_sum" [.scalar (.int n)] heap (.scalar (.int (2 * n + 1)))
      (heap ++ [.list [.scalar (.int n), .scalar (.int (n + 1))], .list [.ref heap.length]]) := by
  let finalHeap := heap ++ [Mutable.Object.list [.scalar (.int n), .scalar (.int (n + 1))],
    .list [.ref heap.length]]
  have outer : Mutable.sequence (.ref (heap.length + 1)) finalHeap =
      some (.ok [.ref heap.length], finalHeap) := by simp [Mutable.sequence, finalHeap]
  have inner : Mutable.sequence (.ref heap.length) finalHeap =
      some (.ok [.scalar (.int n), .scalar (.int (n + 1))], finalHeap) := by simp [Mutable.sequence, finalHeap]
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.sum_generator_targets_sequence
    (source := .ref (heap.length + 1)) (middle := finalHeap) (afterStart := finalHeap)
    (by intro expressions impossible; cases impossible)
  · have row : HeapCalls.Evaluates program
        (HeapCalls.argumentEnv [⟨"n", some (.name "int"), none⟩] [.scalar (.int n)])
        (.list [.name "n", .binOp (.name "n") .add (.constant (.int 1))]) heap
        (.ref heap.length) (heap ++ [.list [.scalar (.int n), .scalar (.int (n + 1))]]) :=
      HeapCalls.Evaluates.list (.cons (.lookup rfl)
        (.cons (HeapCalls.Evaluates.binary (.lookup rfl) .constant rfl) .nil))
    have evaluated := HeapCalls.Evaluates.list (.cons row .nil)
    simpa [finalHeap, List.append_assoc] using evaluated
  · exact outer
  · exact .constant
  · rfl
  · apply HeapCalls.BlockReturns.sequence_step (source := .ref (heap.length + 1)) (heap := finalHeap) outer rfl
    apply HeapCalls.BlockReturns.unpack (items := [.scalar (.int n), .scalar (.int (n + 1))])
      (afterUnpack := finalHeap) rfl (HeapCalls.Evaluates.lookup rfl) inner rfl
    apply HeapCalls.BlockReturns.assign (value := .scalar (.int (n + (n + 1)))) (middle := finalHeap)
    · exact HeapCalls.Evaluates.binary (.lookup rfl)
        (HeapCalls.Evaluates.binary (.lookup rfl) (.lookup rfl) rfl)
        (by simp [Mutable.binary, scalarBinary])
    · apply HeapCalls.BlockReturns.sequence_done (source := .ref (heap.length + 1)) (heap := finalHeap) outer rfl
      apply HeapCalls.BlockReturns.return_value
      apply HeapCalls.Evaluates.lookup
      simp [HeapCalls.setLocal]
      omega

theorem pair_sum.«Returns» (n : Int) :
    (HeapCalls.scalarFunction program "pair_sum" [.int n]).Returns :=
  (pair_sum.result n []).scalar_returns

theorem pair_sum.«Supported» (n : Int) :
    (HeapCalls.scalarFunction program "pair_sum" [.int n]).Supported :=
  (pair_sum.«Returns» n).supported

end tests.py.unpacked_comprehensions
