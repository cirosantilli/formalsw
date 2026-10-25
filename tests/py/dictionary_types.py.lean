import «.formalsw».tests.py.«dictionary_types.py.ast»
import lang.py.FormalSW.HeapCalls
import lang.py.FormalSW.ContainerTypes

namespace tests.py.dictionary_types
open FormalSW.PyAst
private abbrev program := DictionaryTypesAst.module
private abbrev mapping : Mutable.ContainerType :=
  .dictionary (.scalar "int") (.dictionary (.tuple [.scalar "int", .scalar "int"]) (.list (.scalar "int")))

theorem keep.result (heap : Mutable.Heap) (address : Nat) :
    HeapCalls.ReturnsValue program "keep" [.ref address] heap (.ref address) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup rfl)

theorem keep.«Returns» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (_typed : Mutable.Value.HasContainerType heap (.ref address) mapping) :
    (HeapCalls.call program "keep" [.ref address] heap).Returns := (keep.result heap address).returns

theorem keep.«ReturnType» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasContainerType heap (.ref address) mapping) :
    (HeapCalls.call program "keep" [.ref address] heap).ReturnContainerType mapping :=
  .inr ⟨.ref address, [], heap, heap.length, (keep.result heap address).finishes, typed⟩

theorem keep.«Supported» (heap : Mutable.Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasContainerType heap (.ref address) mapping) :
    (HeapCalls.call program "keep" [.ref address] heap).Supported :=
  (keep.«Returns» heap address valid typed).supported

end tests.py.dictionary_types
