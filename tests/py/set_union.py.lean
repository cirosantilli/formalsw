import «.formalsw».tests.py.«set_union.py.ast»
import FormalSW

namespace tests.py.set_union
open FormalSW.PyAst FormalSW.PyAst.HeapCalls

private abbrev program := SetUnionAst.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)

private theorem singleton (env : HeapCalls.Env) (heap : Mutable.Heap) (n : Int)
    (getN : env "n" = some (number n)) :
    Evaluates program env (.builtinCall .setDisplay [.name "n"]) heap (.ref heap.length)
      (heap ++ [.set [.int n]]) := by
  apply Evaluates.builtin (.cons (Evaluates.lookup getN) .nil)
  exact Mutable.allocateSetValues_singleton heap (.int n)

private theorem extended.result (heap : Mutable.Heap) (address : Nat) (items : List Constant) (n : Int)
    (found : heap[address]? = some (.set items)) :
    ReturnsValue program "extended" [.ref address, number n] heap (.ref (heap.length + 1))
      ((heap ++ [.set [.int n]]) ++ [.set (ScalarSet.insert items (.int n))]) := by
  have left : (heap ++ [.set [.int n]])[address]? = some (.set items) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary (middle := heap) (afterRight := heap ++ [.set [.int n]])
    (Evaluates.lookup rfl) (singleton _ heap n rfl)
  have operation := Mutable.binary_union_sets (heap ++ [.set [.int n]]) address heap.length items [.int n] left (by simp)
  simpa only [ScalarSet.union_singleton, List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
    List.append_assoc, List.singleton_append] using operation

theorem extended.«Returns» (heap : Mutable.Heap) (address : Nat) (n : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "set[int]") :
    (HeapCalls.call program "extended" [.ref address, number n] heap).Returns := by
  obtain ⟨items, found, _⟩ := typed
  exact (extended.result heap address items n found).returns

theorem extended.«Supported» (heap : Mutable.Heap) (address : Nat) (n : Int)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "set[int]") :
    (HeapCalls.call program "extended" [.ref address, number n] heap).Supported :=
  (extended.«Returns» heap address n valid typed).supported

private theorem updated.result (heap : Mutable.Heap) (address : Nat) (items : List Constant) (n : Int)
    (found : heap[address]? = some (.set items)) :
    ReturnsValue program "updated" [.ref address, number n] heap (.ref address)
      ((heap ++ [Mutable.Object.set [.int n]]).set address (.set (ScalarSet.insert items (.int n)))) := by
  have left : (heap ++ [.set [.int n]])[address]? = some (.set items) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  apply BlockReturns.function rfl rfl
  apply BlockReturns.augAssign rfl (singleton _ heap n rfl)
  · simpa [ScalarSet.union] using
      HeapCalls.inplace_union_sets (heap ++ [.set [.int n]]) address heap.length items [.int n] left (by simp)
  · exact BlockReturns.return_value (Evaluates.lookup rfl)

theorem updated.«Returns» (heap : Mutable.Heap) (address : Nat) (n : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "set[int]") :
    (HeapCalls.call program "updated" [.ref address, number n] heap).Returns := by
  obtain ⟨items, found, _⟩ := typed
  exact (updated.result heap address items n found).returns

theorem updated.«Supported» (heap : Mutable.Heap) (address : Nat) (n : Int)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "set[int]") :
    (HeapCalls.call program "updated" [.ref address, number n] heap).Supported :=
  (updated.«Returns» heap address n valid typed).supported

end tests.py.set_union
