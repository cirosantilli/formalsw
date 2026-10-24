import «.formalsw».tests.py.«identity.py.ast»
import FormalSW

namespace tests.py.identity
open FormalSW.PyAst
private abbrev program := IdentityAst.module

theorem not_none.result (n : Int) :
    Calls.ReturnsValue program "not_none" [.int n] (.bool true) := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  apply Calls.Evaluates.unary
  · exact Calls.Evaluates.builtin (.cons (Calls.Evaluates.lookup rfl) (.cons .constant .nil)) rfl
  · rfl

theorem not_none.«Returns» (n : Int) : (Calls.function program "not_none" [.int n]).Returns :=
  (not_none.result n).returns

theorem same.result (heap : Mutable.Heap) (xs ys : Nat) :
    HeapCalls.ReturnsValue program "same" [.ref xs, .ref ys] heap (.scalar (.bool (xs == ys))) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  exact HeapCalls.Evaluates.builtin
    (.cons (HeapCalls.Evaluates.lookup rfl) (.cons (HeapCalls.Evaluates.lookup rfl) .nil)) rfl

theorem same.«Returns» (heap : Mutable.Heap) (xs ys : Nat)
    (_valid : Mutable.Heap.Valid heap)
    (_xs : Mutable.Value.HasType heap (.ref xs) "list[int]")
    (_ys : Mutable.Value.HasType heap (.ref ys) "list[int]") :
    (HeapCalls.call program "same" [.ref xs, .ref ys] heap).Returns :=
  (same.result heap xs ys).returns

theorem same.«Supported» (heap : Mutable.Heap) (xs ys : Nat)
    (_valid : Mutable.Heap.Valid heap)
    (_xs : Mutable.Value.HasType heap (.ref xs) "list[int]")
    (_ys : Mutable.Value.HasType heap (.ref ys) "list[int]") :
    (HeapCalls.call program "same" [.ref xs, .ref ys] heap).Supported :=
  (same.result heap xs ys).returns.supported

end tests.py.identity
