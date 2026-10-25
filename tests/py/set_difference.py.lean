import «.formalsw».tests.py.«set_difference.py.ast»
import FormalSW

namespace tests.py.set_difference
open FormalSW.PyAst HeapCalls
set_option Elab.async false
private abbrev program := SetDifferenceAst.module

theorem difference.result (heap : Mutable.Heap) (left right : Nat) (xs ys : List Constant)
    (leftFound : heap[left]? = some (.set xs)) (rightFound : heap[right]? = some (.set ys)) :
    ReturnsValue program "difference" [.ref left, .ref right] heap (.ref heap.length)
      (heap ++ [.set (ScalarSet.difference xs ys)]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.binary (middle := heap) (afterRight := heap)
    (Evaluates.lookup rfl) (Evaluates.lookup rfl)
    (Mutable.binary_difference_sets heap left right xs ys leftFound rightFound)

theorem difference.«Returns» (heap : Mutable.Heap) (left right : Nat) (_valid : heap.Valid)
    (leftTyped : Mutable.Value.HasType heap (.ref left) "set[int]")
    (rightTyped : Mutable.Value.HasType heap (.ref right) "set[int]") :
    (HeapCalls.call program "difference" [.ref left, .ref right] heap).Returns := by
  obtain ⟨xs, leftFound, _⟩ := leftTyped
  obtain ⟨ys, rightFound, _⟩ := rightTyped
  exact (difference.result heap left right xs ys leftFound rightFound).returns

theorem difference.«Supported» (heap : Mutable.Heap) (left right : Nat) (valid : heap.Valid)
    (leftTyped : Mutable.Value.HasType heap (.ref left) "set[int]")
    (rightTyped : Mutable.Value.HasType heap (.ref right) "set[int]") :
    (HeapCalls.call program "difference" [.ref left, .ref right] heap).Supported :=
  (difference.«Returns» heap left right valid leftTyped rightTyped).supported

theorem subtract.result (heap : Mutable.Heap) (left right : Nat) (xs ys : List Constant)
    (leftFound : heap[left]? = some (.set xs)) (rightFound : heap[right]? = some (.set ys)) :
    ReturnsValue program "subtract" [.ref left, .ref right] heap (.ref left)
      (heap.set left (.set (ScalarSet.difference xs ys))) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.augAssign rfl (Evaluates.lookup rfl)
    (inplace_difference_sets heap left right xs ys leftFound rightFound)
  exact BlockReturns.return_value (Evaluates.lookup rfl)

theorem subtract.«Returns» (heap : Mutable.Heap) (left right : Nat) (_valid : heap.Valid)
    (leftTyped : Mutable.Value.HasType heap (.ref left) "set[int]")
    (rightTyped : Mutable.Value.HasType heap (.ref right) "set[int]") :
    (HeapCalls.call program "subtract" [.ref left, .ref right] heap).Returns := by
  obtain ⟨xs, leftFound, _⟩ := leftTyped
  obtain ⟨ys, rightFound, _⟩ := rightTyped
  exact (subtract.result heap left right xs ys leftFound rightFound).returns

theorem subtract.«Supported» (heap : Mutable.Heap) (left right : Nat) (valid : heap.Valid)
    (leftTyped : Mutable.Value.HasType heap (.ref left) "set[int]")
    (rightTyped : Mutable.Value.HasType heap (.ref right) "set[int]") :
    (HeapCalls.call program "subtract" [.ref left, .ref right] heap).Supported :=
  (subtract.«Returns» heap left right valid leftTyped rightTyped).supported

end tests.py.set_difference
