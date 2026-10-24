import «.formalsw».tests.py.«sorted_keys.py.ast»
import lang.py.FormalSW.HeapCalls

namespace tests.py.sorted_keys
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := SortedKeysAst.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private def pairs (key : Int → Int) (items : List Int) : List (Mutable.Value × Int) :=
  items.map fun value => (number value, key value)
private def output (key : Int → Int) (items : List Int) : List Mutable.Value :=
  (HeapSort.keyInts (pairs key items)).map Prod.fst

/-- All callbacks finish in input order before the integer-key sort begins. -/
private theorem keys_result (cursor : SequenceSort) (key : Int → Int) (heap : Mutable.Heap)
    (remaining done : List Int) (direction : cursor.reverse = false)
    (evaluated : ∀ value, Evaluates program (setLocal cursor.env cursor.parameter (number value))
      cursor.key heap (number (key value)) heap) :
    SortedReturns program cursor (remaining.map number)
      ((pairs key done).map HeapSort.intKey) heap (.ref heap.length)
      (heap ++ [.list (output key (done.reverse ++ remaining))]) := by
  induction remaining generalizing done with
  | nil =>
      apply SortedReturns.done
      have ordered : HeapSort.keyedSortWithReverse heap cursor.reverse
          ((pairs key done).map HeapSort.intKey).reverse =
          some (.ok ((HeapSort.keyInts (pairs key done.reverse)).map HeapSort.intKey)) := by
        rw [direction]
        change HeapSort.keyedSort heap ((pairs key done).map HeapSort.intKey).reverse = _
        rw [← List.map_reverse, HeapSort.keyedSort_intkeys]
        simp only [pairs, List.map_reverse]
      simp [sortedFinish, ordered, output, HeapSort.intKey, List.map_map, Mutable.allocate, Except.map]
  | cons value rest ih =>
      apply SortedReturns.next (evaluated value)
      simpa [pairs, List.reverse_cons, List.append_assoc] using ih (value :: done)

theorem identity.result (heap : Mutable.Heap) (address : Nat) (items : List Int)
    (found : heap[address]? = some (.list (items.map number))) :
    ReturnsValue program "identity" [.ref address] heap (.ref heap.length)
      (heap ++ [.list (output id items)]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sorted_sequence (Evaluates.lookup rfl) (Evaluates.constant)
    (items := items.map number) (direction := false) (middle := heap)
  · simp [sortedStart, sortedItems, Mutable.sequence, found, Mutable.truth, scalarTruth]
  · apply keys_result _ id heap items [] rfl
    intro value
    exact Evaluates.lookup (by simp [setLocal])

theorem negated.result (heap : Mutable.Heap) (address : Nat) (items : List Int)
    (found : heap[address]? = some (.list (items.map number))) :
    ReturnsValue program "negated" [.ref address] heap (.ref heap.length)
      (heap ++ [.list (output Neg.neg items)]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sorted_sequence (Evaluates.lookup rfl) (Evaluates.constant)
    (items := items.map number) (direction := false) (middle := heap)
  · simp [sortedStart, sortedItems, Mutable.sequence, found, Mutable.truth, scalarTruth]
  · apply keys_result _ Neg.neg heap items [] rfl
    intro value
    exact Evaluates.unary (value := number value) (Evaluates.lookup (by simp [setLocal])) rfl

theorem identity.«Returns» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "identity" [.ref address] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (identity.result heap address items found).returns

theorem negated.«Returns» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "negated" [.ref address] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (negated.result heap address items found).returns

theorem identity.«Supported» (heap : Mutable.Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "identity" [.ref address] heap).Supported :=
  (identity.«Returns» heap address valid typed).supported

theorem negated.«Supported» (heap : Mutable.Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "negated" [.ref address] heap).Supported :=
  (negated.«Returns» heap address valid typed).supported

end tests.py.sorted_keys
