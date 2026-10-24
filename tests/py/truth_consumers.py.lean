import «.formalsw».tests.py.«truth_consumers.py.ast»
import lang.py.FormalSW.TruthCalls

namespace tests.py.truth_consumers
open FormalSW.PyAst
private abbrev program := TruthConsumersAst.module

theorem positive.result (heap : Mutable.Heap) (address : Nat) (items : List Int)
    (found : heap[address]? = some (.list (items.map fun n => .scalar (.int n)))) :
    HeapCalls.ReturnsValue program "positive" [.ref address] heap
      (.scalar (.bool (decide (∀ n ∈ items, 0 < n)))) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.all_positive (HeapCalls.Evaluates.lookup rfl)
  simp [Mutable.sequence, found]

theorem positive.«Returns» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "positive" [.ref address] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (positive.result heap address items found).returns

theorem positive.«Supported» (heap : Mutable.Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "positive" [.ref address] heap).Supported :=
  (positive.«Returns» heap address valid typed).supported

end tests.py.truth_consumers
