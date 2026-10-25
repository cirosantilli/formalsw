import «.formalsw».tests.py.«nested_sort.py.ast»
import lang.py.FormalSW.HeapSortingCalls

namespace tests.py.nested_sort
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := NestedSortAst.module

def sortedRows (heap : Heap) (addresses : List Nat) : List Mutable.Value :=
  HeapSort.sortBy (fun left right => HeapSort.lexInt (HeapSort.readInts heap left) (HeapSort.readInts heap right))
    (addresses.map Mutable.Value.ref)

theorem ascending.result (heap : Heap) (address : Nat) (rows : List Nat)
    (found : heap[address]? = some (.list (rows.map Mutable.Value.ref)))
    (typed : ∀ row ∈ rows, Mutable.Value.HasType heap (.ref row) "list[int]") :
    ReturnsValue program "ascending" [.ref address] heap (.ref heap.length)
      (heap ++ [.list (sortedRows heap rows)]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.builtin (.cons (Evaluates.lookup rfl) .nil)
  exact primitive_sorted_values heap address _ _ found (HeapSort.sort_int_lists heap rows typed)

theorem sortedRows_perm (heap : Heap) (rows : List Nat) :
    (sortedRows heap rows).Perm (rows.map Mutable.Value.ref) := HeapSort.sortBy_perm _ _

theorem ascending.«Returns» (heap : Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    (HeapCalls.call program "ascending" [.ref address] heap).Returns := by
  obtain ⟨rows, found, types⟩ := Mutable.Value.lists_of_hasType typed
  exact (ascending.result heap address rows found types).returns

theorem ascending.«Supported» (heap : Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    (HeapCalls.call program "ascending" [.ref address] heap).Supported :=
  (ascending.«Returns» heap address valid typed).supported

end tests.py.nested_sort
