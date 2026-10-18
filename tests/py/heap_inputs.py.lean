import «.formalsw».tests.py.«heap_inputs.py.ast»
import FormalSW

namespace tests.py.heap_inputs
open FormalSW.PyAst
private abbrev program := HeapInputsAst.module

private theorem identity.result (heap : Mutable.Heap) (xs : Nat) :
    HeapCalls.ReturnsValue program "identity" [.ref xs] heap (.ref xs) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup rfl)

private theorem reference.result (heap : Mutable.Heap) (xs : Nat) :
    HeapCalls.ReturnsValue program "reference" [.ref xs] heap (.ref xs) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup rfl)

private abbrev inputEnv (xs : Nat) : HeapCalls.Env :=
  fun name => if name = "xs" then some (.ref xs) else none

private theorem identity.condition (heap : Mutable.Heap) (xs : Nat)
    (typed : Mutable.Value.HasType heap (.ref xs) "list[int]") :
    HeapCalls.Evaluates program (inputEnv xs) HeapInputsAst.requires_identity_0 heap
      (.scalar (.bool true)) heap := by
  obtain ⟨items, found, _⟩ := typed
  apply HeapCalls.Evaluates.compare (av := .scalar (.int items.length)) (middle := heap) (afterRight := heap)
  · exact HeapCalls.Evaluates.builtin (.cons (HeapCalls.Evaluates.lookup rfl) .nil)
      (by simp [HeapCalls.primitive, Mutable.length, found])
  · exact HeapCalls.Evaluates.constant
  · simp [HeapCalls.compare, scalarCompare, evalCmpOp]

theorem requires_identity_0_supported (heap : Mutable.Heap) (xs : Nat)
    (_valid : Mutable.Heap.Valid heap) (typed : Mutable.Value.HasType heap (.ref xs) "list[int]") :
    (HeapCalls.evaluate program (inputEnv xs) HeapInputsAst.requires_identity_0 heap).Supported :=
  Execution.supported_of_finishes (identity.condition heap xs typed).finishes

theorem identity.«Returns» (heap : Mutable.Heap) (xs : Nat)
    (_valid : Mutable.Heap.Valid heap) (_typed : Mutable.Value.HasType heap (.ref xs) "list[int]")
    (_requires : HeapCalls.Condition program (inputEnv xs) HeapInputsAst.requires_identity_0 heap) :
    (HeapCalls.call program "identity" [.ref xs] heap).Returns :=
  (identity.result heap xs).returns

theorem identity.raw (heap : Mutable.Heap) (xs : Nat)
    (inputs : Mutable.Heap.Valid heap ∧ Mutable.Value.HasType heap (.ref xs) "list[int]" ∧
      HeapCalls.Condition program (inputEnv xs) HeapInputsAst.requires_identity_0 heap) :
    (HeapCalls.call program "identity" [.ref xs] heap).Returns :=
  identity.«Returns» heap xs inputs.1 inputs.2.1 inputs.2.2

theorem identity.«Equiv(reference)» (heap : Mutable.Heap) (xs : Nat)
    (_valid : Mutable.Heap.Valid heap) (_typed : Mutable.Value.HasType heap (.ref xs) "list[int]")
    (_requires : HeapCalls.Condition program (inputEnv xs) HeapInputsAst.requires_identity_0 heap) :
    (HeapCalls.call program "identity" [.ref xs] heap).Equiv
      (HeapCalls.call program "reference" [.ref xs] heap) :=
  Mutable.Call.equiv_of_finishes (identity.result heap xs).finishes (reference.result heap xs).finishes (.inl rfl)

theorem identity.«ReturnType» (heap : Mutable.Heap) (xs : Nat)
    (_valid : Mutable.Heap.Valid heap) (typed : Mutable.Value.HasType heap (.ref xs) "list[int]")
    (_requires : HeapCalls.Condition program (inputEnv xs) HeapInputsAst.requires_identity_0 heap) :
    (HeapCalls.call program "identity" [.ref xs] heap).ReturnType "list[int]" :=
  .inr ⟨.ref xs, [], heap, heap.length, (identity.result heap xs).finishes, typed⟩

theorem identity.«Supported» :
    (∀ (heap : Mutable.Heap) (xs : Nat), Mutable.Heap.Valid heap →
      Mutable.Value.HasType heap (.ref xs) "list[int]" →
      HeapCalls.Condition program (inputEnv xs) HeapInputsAst.requires_identity_0 heap →
      (HeapCalls.call program "identity" [.ref xs] heap).Supported) ∧
    (∀ (heap : Mutable.Heap) (xs : Nat), Mutable.Heap.Valid heap →
      Mutable.Value.HasType heap (.ref xs) "list[int]" →
      HeapCalls.Condition program (inputEnv xs) HeapInputsAst.requires_identity_0 heap →
      (HeapCalls.call program "reference" [.ref xs] heap).Supported) :=
  ⟨fun heap xs _ _ _ => (identity.result heap xs).returns.supported,
   fun heap xs _ _ _ => (reference.result heap xs).returns.supported⟩

private theorem keep.result (heap : Mutable.Heap) (left right : Nat) :
    HeapCalls.ReturnsValue program "keep" [.ref left, .ref right] heap (.ref right) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup rfl)

theorem keep.«Returns» (heap : Mutable.Heap) (left right : Nat)
    (_valid : Mutable.Heap.Valid heap)
    (_left : Mutable.Value.HasType heap (.ref left) "list[int]")
    (_right : Mutable.Value.HasType heap (.ref right) "list[int]") :
    (HeapCalls.call program "keep" [.ref left, .ref right] heap).Returns :=
  (keep.result heap left right).returns

theorem keep.«Supported» (heap : Mutable.Heap) (left right : Nat)
    (_valid : Mutable.Heap.Valid heap)
    (_left : Mutable.Value.HasType heap (.ref left) "list[int]")
    (_right : Mutable.Value.HasType heap (.ref right) "list[int]") :
    (HeapCalls.call program "keep" [.ref left, .ref right] heap).Supported :=
  (keep.result heap left right).returns.supported

end tests.py.heap_inputs
