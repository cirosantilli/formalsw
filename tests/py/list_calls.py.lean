import «.formalsw».tests.py.«list_calls.py.ast»
import lang.py.FormalSW.HeapCalls

namespace tests.py.list_calls
open FormalSW.PyAst
private abbrev program := ListCallsAst.module

/-- The outer list is fresh; its elements retain their original identities. -/
theorem copy.result (heap : Mutable.Heap) (address : Nat) (items : List Mutable.Value)
    (found : heap[address]? = some (.list items)) :
    HeapCalls.ReturnsValue program "copy" [.ref address] heap (.ref heap.length)
      (heap ++ [.list items]) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  exact HeapCalls.Evaluates.builtin (.cons (HeapCalls.Evaluates.lookup rfl) .nil)
    (HeapCalls.primitive_list_list heap address items found)

theorem copy.«Returns» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "copy" [.ref address] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (copy.result heap address _ found).returns

theorem copy.«ReturnType» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "copy" [.ref address] heap).ReturnType "list[int]" := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  refine .inr ⟨.ref heap.length, [], _, heap.length, (copy.result heap address _ found).finishes, ?_⟩
  simp [Mutable.Value.HasType]
  exact ⟨"int", rfl, by simp⟩

theorem copy.«Supported» (heap : Mutable.Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "copy" [.ref address] heap).Supported :=
  (copy.«Returns» heap address valid typed).supported

private theorem empty.result :
    HeapCalls.ReturnsValue program "empty" [] [] (.ref 0) [.list []] := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  exact HeapCalls.Evaluates.builtin .nil rfl

theorem empty.«Returns» : (HeapCalls.call program "empty" [] []).Returns :=
  empty.result.returns

theorem empty.«Supported» : (HeapCalls.call program "empty" [] []).Supported :=
  empty.«Returns».supported

end tests.py.list_calls
