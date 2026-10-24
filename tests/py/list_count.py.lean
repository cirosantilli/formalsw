import «.formalsw».tests.py.«list_count.py.ast»
import lang.py.FormalSW.HeapCalls

namespace tests.py.list_count
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := ListCountAst.module

/-- The source counts every occurrence in an arbitrary integer list and preserves the heap exactly. -/
theorem occurrences.result (heap : Mutable.Heap) (address : Nat) (items : List Int) (value : Int)
    (found : heap[address]? = some (.list (items.map fun item => .scalar (.int item)))) :
    ReturnsValue program "occurrences" [.ref address, .scalar (.int value)] heap
      (.scalar (.int (items.count value))) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.count (Evaluates.lookup rfl) found (.cons (Evaluates.lookup rfl) .nil)
    (primitive_count_list heap address items value found)
  intro name same
  cases same
  rfl

theorem occurrences.«Returns» (heap : Mutable.Heap) (address : Nat) (value : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "occurrences" [.ref address, .scalar (.int value)] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (occurrences.result heap address items value found).returns

theorem occurrences.«ReturnType» (heap : Mutable.Heap) (address : Nat) (value : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "occurrences" [.ref address, .scalar (.int value)] heap).ReturnType "int" := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact .inr ⟨_, [], heap, heap.length, (occurrences.result heap address items value found).finishes, rfl⟩

theorem occurrences.«Supported» (heap : Mutable.Heap) (address : Nat) (value : Int)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "occurrences" [.ref address, .scalar (.int value)] heap).Supported :=
  (occurrences.«Returns» heap address value valid typed).supported

end tests.py.list_count
