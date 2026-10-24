import lang.py.FormalSW.HeapCalls

/-! Source comparison rules retain the caller's heap and tuple identities. -/
namespace FormalSW.PyAst.HeapCalls

theorem compare_tuple_lt (heap : Heap) (a b : Nat) (xs ys : List Mutable.Value) (answer : Bool)
    (left : heap[a]? = some (.tuple xs)) (right : heap[b]? = some (.tuple ys))
    (compared : HeapSort.compare (heap.length+1) heap false (.ref a) (.ref b) = some (.ok answer)) :
    compare .lt (.ref a) (.ref b) heap = some (.ok (.scalar (.bool answer)), heap) := by
  simp [compare, left, right, sequenceCompare, compared]

theorem compare_tuple_gt (heap : Heap) (a b : Nat) (xs ys : List Mutable.Value) (answer : Bool)
    (left : heap[a]? = some (.tuple xs)) (right : heap[b]? = some (.tuple ys))
    (compared : HeapSort.compare (heap.length+1) heap false (.ref b) (.ref a) = some (.ok answer)) :
    compare .gt (.ref a) (.ref b) heap = some (.ok (.scalar (.bool answer)), heap) := by
  simp [compare, left, right, sequenceCompare, compared]

private theorem positive_heap (heap : Heap) (address : Nat) (object : Mutable.Object)
    (found : heap[address]? = some object) : 0 < heap.length := by
  by_cases positive : 0 < heap.length
  · exact positive
  · have missing := List.getElem?_eq_none (show heap.length ≤ address by omega)
    rw [missing] at found
    cases found

/-- Unequal leading integers decide the result without inspecting any later fields. -/
theorem compare_tuple_head_gt (heap : Heap) (a b : Nat) (x y : Int) (xs ys : List Mutable.Value)
    (left : heap[a]? = some (.tuple (.scalar (.int x) :: xs)))
    (right : heap[b]? = some (.tuple (.scalar (.int y) :: ys))) (different : x ≠ y) :
    compare .gt (.ref a) (.ref b) heap = some (.ok (.scalar (.bool (decide (y < x)))), heap) := by
  have positive := positive_heap heap a _ left
  have room : heap.length = (heap.length-1)+1 := by omega
  apply compare_tuple_gt heap a b _ _ _ left right
  rw [room]
  simp [HeapSort.compare, right, left, HeapSort.lex, scalarCompare, evalCmpOp, Ne.symm different]

/-- Arbitrary integer tuples compare lexicographically, including empty tuples and aliases. -/
theorem compare_int_tuple_lt (heap : Heap) (a b : Nat) (xs ys : List Int)
    (left : heap[a]? = some (.tuple (xs.map fun n => .scalar (.int n))))
    (right : heap[b]? = some (.tuple (ys.map fun n => .scalar (.int n)))) :
    compare .lt (.ref a) (.ref b) heap = some (.ok (.scalar (.bool (HeapSort.lexInt xs ys))), heap) := by
  have positive := positive_heap heap a _ left
  have depth : heap.length-1+2 = heap.length+1 := by omega
  apply compare_tuple_lt heap a b _ _ _ left right
  simpa only [depth] using HeapSort.compare_int_tuples heap a b (heap.length-1) xs ys left right

theorem compare_int_tuple_gt (heap : Heap) (a b : Nat) (xs ys : List Int)
    (left : heap[a]? = some (.tuple (xs.map fun n => .scalar (.int n))))
    (right : heap[b]? = some (.tuple (ys.map fun n => .scalar (.int n)))) :
    compare .gt (.ref a) (.ref b) heap = some (.ok (.scalar (.bool (HeapSort.lexInt ys xs))), heap) := by
  have positive := positive_heap heap a _ left
  have depth : heap.length-1+2 = heap.length+1 := by omega
  apply compare_tuple_gt heap a b _ _ _ left right
  simpa only [depth] using HeapSort.compare_int_tuples heap b a (heap.length-1) ys xs right left

end FormalSW.PyAst.HeapCalls
