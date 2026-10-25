import «.formalsw».tests.py.«pop_calls.py.ast»
import lang.py.FormalSW.HeapCalls

namespace tests.py.pop_calls
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := PopCallsAst.module

/-- The source removes the first element, preserving its reference when it has one. -/
theorem take_first.nonempty (heap : Mutable.Heap) (address : Nat)
    (first : Mutable.Value) (rest : List Mutable.Value)
    (found : heap[address]? = some (.list (first :: rest))) :
    ReturnsValue program "take_first" [.ref address] heap first (heap.set address (.list rest)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.branch (flag := true) (Evaluates.lookup rfl)
  · simp [Mutable.truth, found]
  · apply BlockReturns.return_value
    apply Evaluates.pop rfl (by simp [bindMethod, found]) (.cons Evaluates.constant .nil)
    simpa [primitive] using Mutable.popItem_list heap address 0 (first :: rest) found (by simp)

theorem take_first.empty (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list [])) :
    ReturnsValue program "take_first" [.ref address] heap (.scalar (.int 0)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.branch (flag := false) (Evaluates.lookup rfl)
  · simp [Mutable.truth, found]
  · exact BlockReturns.return_value Evaluates.constant

theorem take_first.«Returns» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "take_first" [.ref address] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  cases items with
  | nil => exact (take_first.empty heap address found).returns
  | cons first rest => exact (take_first.nonempty heap address _ _ found).returns

theorem take_first.«Supported» (heap : Mutable.Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "take_first" [.ref address] heap).Supported :=
  (take_first.«Returns» heap address valid typed).supported

end tests.py.pop_calls
