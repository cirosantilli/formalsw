import «.formalsw».tests.py.«list_sort.py.ast»
import FormalSW

namespace tests.py.list_sort
open FormalSW.PyAst
private abbrev program := ListSortAst.module
private def values (items : List Int) := items.map (fun n => Mutable.Value.scalar (.int n))

/-- The original reference and all its aliases see exactly the sorted integers. -/
theorem in_place.result (heap : Mutable.Heap) (address : Nat) (items : List Int)
    (found : heap[address]? = some (.list (values items))) :
    HeapCalls.ReturnsValue program "in_place" [.ref address] heap (.ref address)
      (heap.set address (.list (values (ScalarSort.ints items)))) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.discard
  · apply HeapCalls.Evaluates.sort (HeapCalls.Evaluates.lookup rfl) found
    · simpa [values, List.map_map, Function.comp_def] using
        HeapCalls.primitive_sort_list heap address (items.map Constant.int)
          ((ScalarSort.ints items).map Constant.int)
          (by simpa [values, List.map_map, Function.comp_def] using found) (ScalarSort.sort_ints items)
    · intro name same
      cases same
      rfl
  · exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup rfl)

theorem in_place.«Returns» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "in_place" [.ref address] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (in_place.result heap address items found).returns

theorem in_place.«ReturnType» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "in_place" [.ref address] heap).ReturnType "list[int]" := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  have within : address<heap.length := List.getElem?_eq_some_iff.mp found |>.1
  refine .inr ⟨.ref address, [], _, heap.length, (in_place.result heap address items found).finishes, ?_⟩
  simp [Mutable.Value.HasType, values, List.getElem?_set_self within]
  exact ⟨"int", rfl, by simp⟩

theorem in_place.«Supported» (heap : Mutable.Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "in_place" [.ref address] heap).Supported :=
  (in_place.«Returns» heap address valid typed).supported

end tests.py.list_sort
