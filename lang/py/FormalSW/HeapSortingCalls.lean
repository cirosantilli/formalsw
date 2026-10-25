import lang.py.FormalSW.HeapCalls

namespace FormalSW.PyAst.HeapCalls

/-- Sorting allocates only the result list, preserving every element reference. -/
theorem primitive_sorted_values (heap : Heap) (address : Nat) (items sorted : List Value)
    (found : heap[address]? = some (.list items))
    (ordered : HeapSort.sort heap items = some (.ok sorted)) :
    primitive (.builtin .sorted) [.ref address] heap =
      some (.ok (.ref heap.length), heap ++ [.list sorted]) := by
  simp [primitive, found, Mutable.sequence, ordered, Mutable.allocate, Except.map]

theorem primitive_sorted_tuple_values (heap : Heap) (address : Nat) (items sorted : List Value)
    (found : heap[address]? = some (.tuple items))
    (ordered : HeapSort.sort heap items = some (.ok sorted)) :
    primitive (.builtin .sorted) [.ref address] heap =
      some (.ok (.ref heap.length), heap ++ [.list sorted]) := by
  simp [primitive, found, Mutable.sequence, ordered, Mutable.allocate, Except.map]

end FormalSW.PyAst.HeapCalls
