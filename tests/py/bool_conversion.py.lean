import «.formalsw».tests.py.«bool_conversion.py.ast»
import lang.py.FormalSW.HeapCalls

namespace tests.py.bool_conversion
open FormalSW.PyAst
private abbrev program := BoolConversionAst.module

theorem empty.result : Calls.ReturnsValue program "empty" [] (.bool false) := by
  apply Calls.BlockReturns.function rfl rfl
  exact Calls.BlockReturns.return_value Calls.Evaluates.constant

theorem empty.«Returns» : (Calls.function program "empty" []).Returns := empty.result.returns

theorem integer.result (value : Int) :
    Calls.ReturnsValue program "integer" [.int value] (.bool (value != 0)) := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  apply Calls.Evaluates.unary
  · exact Calls.Evaluates.unary (Calls.Evaluates.lookup rfl) rfl
  · simp [scalarExpr, scalarTruth]

theorem integer.«Returns» (value : Int) : (Calls.function program "integer" [.int value]).Returns :=
  (integer.result value).returns

/-- Only the outer list's length matters, even when its elements refer back to it. -/
theorem sequence.result (heap : Mutable.Heap) (address : Nat) (items : List Mutable.Value)
    (found : heap[address]? = some (.list items)) :
    HeapCalls.ReturnsValue program "sequence" [.ref address] heap (.scalar (.bool (!items.isEmpty))) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.unary (value := .scalar (.bool items.isEmpty)) (middle := heap)
  · apply HeapCalls.Evaluates.unary (HeapCalls.Evaluates.lookup rfl)
    simp [HeapCalls.unary, Mutable.truth, found]
  · simp [HeapCalls.unary, Mutable.truth, scalarTruth]

theorem sequence.«Returns» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "sequence" [.ref address] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (sequence.result heap address _ found).returns

theorem sequence.«Supported» (heap : Mutable.Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "sequence" [.ref address] heap).Supported :=
  (sequence.«Returns» heap address valid typed).supported

end tests.py.bool_conversion
