import «.formalsw».tests.py.«tuple_constructor.py.ast»
import lang.py.FormalSW.HeapCalls

namespace tests.py.tuple_constructor
open FormalSW.PyAst
private abbrev program := TupleConstructorAst.module

private theorem allocated (heap : Mutable.Heap) (items : List Mutable.Value) :
    ∃ address finalHeap, Mutable.allocateTuple items heap = some (.ok (.ref address), finalHeap) := by
  by_cases empty : items.isEmpty = true
  · cases found : heap.findIdx? (fun object => decide (object = .tuple [])) with
    | none => exact ⟨heap.length, heap ++ [.tuple []], by simp [Mutable.allocateTuple, empty, found, Except.map]⟩
    | some address => exact ⟨address, heap, by simp [Mutable.allocateTuple, empty, found]⟩
  · exact ⟨heap.length, heap ++ [.tuple items], by simp [Mutable.allocateTuple, empty, Except.map]⟩

/-- Conversion terminates for any caller heap, including an already interned empty tuple. -/
theorem copy.result (heap : Mutable.Heap) (address : Nat) (items : List Mutable.Value)
    (found : heap[address]? = some (.list items)) :
    ∃ result finalHeap, HeapCalls.ReturnsValue program "copy" [.ref address] heap (.ref result) finalHeap := by
  obtain ⟨result, finalHeap, operation⟩ := allocated heap items
  refine ⟨result, finalHeap, ?_⟩
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  exact HeapCalls.Evaluates.builtin (.cons (HeapCalls.Evaluates.lookup rfl) .nil)
    ((HeapCalls.primitive_tuple_list heap address items found).trans operation)

theorem copy.«Returns» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "copy" [.ref address] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  obtain ⟨result, finalHeap, returned⟩ := copy.result heap address _ found
  exact returned.returns

theorem copy.«Supported» (heap : Mutable.Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "copy" [.ref address] heap).Supported :=
  (copy.«Returns» heap address valid typed).supported

theorem empty.result : HeapCalls.ReturnsValue program "empty" [] [] (.ref 0) [.tuple []] := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  exact HeapCalls.Evaluates.builtin .nil rfl

theorem empty.«Returns» : (HeapCalls.call program "empty" [] []).Returns := empty.result.returns

theorem empty.«Supported» : (HeapCalls.call program "empty" [] []).Supported := empty.«Returns».supported

end tests.py.tuple_constructor
