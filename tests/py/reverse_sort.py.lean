import «.formalsw».tests.py.«reverse_sort.py.ast»
import lang.py.FormalSW.ReverseSortingCalls

namespace tests.py.reverse_sort
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := ReverseSortAst.module
private abbrev numbers (items : List Int) : List Mutable.Value := items.map fun n => .scalar (.int n)

private theorem ordered (heap : Heap) (items : List Int) (reverse : Bool) :
    HeapSort.sortWithReverse heap reverse (numbers items) = some (.ok (numbers (sortedInts reverse items))) := by
  simpa only [List.map_map, Function.comp_def] using sortWithReverse_ints heap reverse items

theorem copied.result (heap : Heap) (address : Nat) (items : List Int) (reverse : Bool)
    (found : heap[address]? = some (.list (numbers items))) :
    ReturnsValue program "copied" [.ref address, .scalar (.bool reverse)] heap (.ref heap.length)
      (heap ++ [.list (numbers (sortedInts reverse items))]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.builtin (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil))
  exact primitive_sorted_reverse_list heap address _ _ reverse found (ordered heap items reverse)

theorem in_place.result (heap : Heap) (address : Nat) (items : List Int) (reverse : Bool)
    (found : heap[address]? = some (.list (numbers items))) :
    ReturnsValue program "in_place" [.ref address, .scalar (.bool reverse)] heap (.ref address)
      (heap.set address (.list (numbers (sortedInts reverse items)))) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.discard
  · apply Evaluates.sort_reverse (Evaluates.lookup rfl) found (Evaluates.lookup rfl)
    · simpa only [List.map_map, Function.comp_def] using primitive_sort_reverse_ints heap address items reverse
        (by simpa only [List.map_map, Function.comp_def] using found)
    · intro name equal
      cases equal
      rfl
  · exact BlockReturns.return_value (Evaluates.lookup rfl)

theorem generated.result (heap : Heap) (address : Nat) (items : List Int)
    (found : heap[address]? = some (.list (numbers items))) :
    ReturnsValue program "generated" [.ref address] heap (.ref (heap.length+1))
      (heap ++ [.list (numbers items), .list (numbers (sortedInts true items))]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.consume_generator_sorted_reverse
  apply GeneratorCollects.copy_sequence rfl found
  change primitive (.builtin .sortedReverse) [.ref heap.length, .scalar (.bool true)] (heap ++ [.list (numbers items)]) =
    some (.ok (.ref (heap.length+1)), heap ++ [.list (numbers items), .list (numbers (sortedInts true items))])
  have completed := primitive_sorted_reverse_list (heap ++ [.list (numbers items)]) heap.length _ _ true
    (by simp) (ordered (heap ++ [.list (numbers items)]) items true)
  have size : (heap ++ [Mutable.Object.list (numbers items)]).length = heap.length+1 := by simp
  have merged : (heap ++ [.list (numbers items)]) ++ [.list (numbers (sortedInts true items))] =
      heap ++ [.list (numbers items), .list (numbers (sortedInts true items))] := by
    rw [List.append_assoc]
    rfl
  rw [size, merged] at completed
  exact completed

theorem copied.«Returns» (heap : Heap) (address : Nat) (reverse : Bool)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "copied" [.ref address, .scalar (.bool reverse)] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (copied.result heap address items reverse found).returns

theorem copied.«Supported» (heap : Heap) (address : Nat) (reverse : Bool)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "copied" [.ref address, .scalar (.bool reverse)] heap).Supported :=
  (copied.«Returns» heap address reverse valid typed).supported

theorem in_place.«Returns» (heap : Heap) (address : Nat) (reverse : Bool)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "in_place" [.ref address, .scalar (.bool reverse)] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (in_place.result heap address items reverse found).returns

theorem in_place.«Supported» (heap : Heap) (address : Nat) (reverse : Bool)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "in_place" [.ref address, .scalar (.bool reverse)] heap).Supported :=
  (in_place.«Returns» heap address reverse valid typed).supported

theorem generated.«Returns» (heap : Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "generated" [.ref address] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (generated.result heap address items found).returns

theorem generated.«Supported» (heap : Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "generated" [.ref address] heap).Supported := (generated.«Returns» heap address valid typed).supported

end tests.py.reverse_sort
