import lang.py.FormalSW.HeapqFramedTotal

/-! Concrete heap operations on shared integer tuples, retaining their original references. -/
namespace FormalSW.PyAst.Heapq

def IntegerTuple (heap : Heap) (value : Value) : Prop :=
  ∃ address : Nat, ∃ fields : List Int, value = .ref address ∧
    heap[address]? = some (.tuple (fields.map fun n => .scalar (.int n)))

/-- Only the integer tuples used as comparison keys need to retain their contents. -/
def TupleFrame (original current : Heap) : Prop :=
  ∀ address : Nat, ∀ fields : List Int,
    original[address]? = some (.tuple (fields.map fun n => .scalar (.int n))) →
      current[address]? = some (.tuple (fields.map fun n => .scalar (.int n)))

theorem TupleFrame.refl (heap : Heap) : TupleFrame heap heap := fun _ _ read => read

theorem TupleFrame.replace_list (original : Heap) (address : Nat) (values : List Value)
    (found : original[address]? = some (.list values)) :
    ListReplacementInvariant address (TupleFrame original) := by
  intro heap replacement kept other fields read
  have different : address ≠ other := by
    intro same
    subst other
    rw [found] at read
    cases read
  rw [List.getElem?_set_ne different]
  exact kept other fields read

theorem less_int_tuples (heap : Heap) (left right : Nat) (xs ys : List Int)
    (leftFound : heap[left]? = some (.tuple (xs.map fun n => .scalar (.int n))))
    (rightFound : heap[right]? = some (.tuple (ys.map fun n => .scalar (.int n)))) :
    less (.ref left) (.ref right) heap = some (.ok (HeapSort.lexInt xs ys), heap) := by
  have positive : 0 < heap.length := by
    have inside := (List.getElem?_eq_some_iff.mp leftFound).1
    omega
  have allowance := HeapSort.comparisonFuel_ge_linear heap
  have depth : HeapSort.comparisonFuel heap - 2 + 2 = HeapSort.comparisonFuel heap := by omega
  have compared := HeapSort.compare_int_tuples heap left right (HeapSort.comparisonFuel heap - 2)
    xs ys leftFound rightFound
  rw [depth] at compared
  simp [less, compared]

/-- Pair priorities use the first field, with the second field breaking ties. -/
theorem less_int_pair (heap : Heap) (left right : Nat) (priority tie otherPriority otherTie : Int)
    (leftFound : heap[left]? = some (.tuple [.scalar (.int priority), .scalar (.int tie)]))
    (rightFound : heap[right]? = some (.tuple [.scalar (.int otherPriority), .scalar (.int otherTie)])) :
    less (.ref left) (.ref right) heap =
      some (.ok (if priority = otherPriority then decide (tie < otherTie)
        else decide (priority < otherPriority)), heap) := by
  have compared := less_int_tuples heap left right [priority, tie] [otherPriority, otherTie]
    leftFound rightFound
  by_cases same : tie = otherTie <;> simpa [HeapSort.lexInt, same] using compared

theorem TupleFrame.comparable (original : Heap) :
    ComparisonUnder (TupleFrame original) (IntegerTuple original) := by
  intro heap kept left right leftTyped rightTyped
  obtain ⟨a, xs, rfl, leftFound⟩ := leftTyped
  obtain ⟨b, ys, rfl, rightFound⟩ := rightTyped
  exact ⟨HeapSort.lexInt xs ys, less_int_tuples heap a b xs ys
    (kept a xs leftFound) (kept b ys rightFound)⟩

theorem heapify_int_tuples (heap : Heap) (address : Nat) (values : List Value)
    (found : heap[address]? = some (.list values))
    (typed : ∀ value ∈ values, IntegerTuple heap value) :
    ∃ after, heapify [.ref address] heap = some (.ok (.scalar .none), after) ∧
      Reorders heap address values after := by
  obtain ⟨after, executed⟩ := heapify_succeeds_under (IntegerTuple heap) (TupleFrame heap)
    (TupleFrame.comparable heap) heap address values (TupleFrame.replace_list heap address values found)
    (TupleFrame.refl heap) typed found
  exact ⟨after, executed, heapify_reorders heap after address values (.ok (.scalar .none)) found executed⟩

theorem heappush_int_tuples (heap : Heap) (address : Nat) (values : List Value) (item : Value)
    (found : heap[address]? = some (.list values))
    (typed : ∀ value ∈ values, IntegerTuple heap value) (itemTyped : IntegerTuple heap item) :
    ∃ after, heappush [.ref address, item] heap = some (.ok (.scalar .none), after) ∧
      Reorders heap address (values ++ [item]) after := by
  obtain ⟨after, executed⟩ := heappush_succeeds_under (IntegerTuple heap) (TupleFrame heap)
    (TupleFrame.comparable heap) heap address values item (TupleFrame.replace_list heap address values found)
    (TupleFrame.refl heap) typed itemTyped found
  exact ⟨after, executed, heappush_reorders heap after address values item (.ok (.scalar .none)) found executed⟩

theorem heappop_int_tuples (heap : Heap) (address : Nat) (root : Value) (rest : List Value)
    (found : heap[address]? = some (.list (root :: rest)))
    (typed : ∀ value ∈ root :: rest, IntegerTuple heap value) :
    ∃ after, heappop [.ref address] heap = some (.ok root, after) ∧ Reorders heap address rest after := by
  obtain ⟨after, executed⟩ := heappop_succeeds_under (IntegerTuple heap) (TupleFrame heap)
    (TupleFrame.comparable heap) heap address root rest (TupleFrame.replace_list heap address (root :: rest) found)
    (TupleFrame.refl heap) typed found
  exact ⟨after, executed, heappop_reorders heap after address root rest (.ok root) found executed⟩

end FormalSW.PyAst.Heapq
