import «.formalsw».tests.py.«sorted_calls.py.ast»
import FormalSW

namespace tests.py.sorted_calls
open FormalSW.PyAst
private abbrev program := SortedCallsAst.module
private def values (items : List Int) := items.map (fun n => Mutable.Value.scalar (.int n))

/-- The caller's heap is unchanged and a fresh list contains exactly the sorted integers. -/
theorem ascending.result (heap : Mutable.Heap) (address : Nat) (items : List Int)
    (found : heap[address]? = some (.list (values items))) :
    HeapCalls.ReturnsValue program "ascending" [.ref address] heap (.ref heap.length)
      (heap ++ [.list (values (ScalarSort.ints items))]) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.builtin (.cons (HeapCalls.Evaluates.lookup rfl) .nil)
  simpa [List.map_map, values, Function.comp_def] using
    HeapCalls.primitive_sorted_list heap address (items.map Constant.int)
      ((ScalarSort.ints items).map Constant.int)
      (by simpa [List.map_map, values, Function.comp_def] using found) (ScalarSort.sort_ints items)

theorem ascending.«Returns» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "ascending" [.ref address] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (ascending.result heap address items found).returns

theorem ascending.«ReturnType» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "ascending" [.ref address] heap).ReturnType "list[int]" := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  refine .inr ⟨.ref heap.length, [], _, heap.length, (ascending.result heap address items found).finishes, ?_⟩
  simp [Mutable.Value.HasType, values]
  exact ⟨"int", rfl, by simp⟩

theorem ascending.«Supported» (heap : Mutable.Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "ascending" [.ref address] heap).Supported :=
  (ascending.«Returns» heap address valid typed).supported

end tests.py.sorted_calls
