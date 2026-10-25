import «.formalsw».tests.py.«variadic_tuples.py.ast»
import lang.py.FormalSW.HeapCalls
import lang.py.FormalSW.ContainerTypes

namespace tests.py.variadic_tuples
open FormalSW.PyAst
private abbrev program := VariadicTuplesAst.module
private abbrev strings : Mutable.ContainerType := .tupleOf (.scalar "str")

example (env : HeapCalls.Env) (heap : Mutable.Heap) :
    HeapCalls.step program 0 ⟨.expr .ellipsis env, [], heap⟩ = .unsupported := rfl

theorem keep.result (heap : Mutable.Heap) (address : Nat) :
    HeapCalls.ReturnsValue program "keep" [.ref address] heap (.ref address) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup rfl)

theorem keep.«Returns» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (_typed : Mutable.Value.HasContainerType heap (.ref address) strings) :
    (HeapCalls.call program "keep" [.ref address] heap).Returns := (keep.result heap address).returns

theorem keep.«ReturnType» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasContainerType heap (.ref address) strings) :
    (HeapCalls.call program "keep" [.ref address] heap).ReturnContainerType strings :=
  .inr ⟨.ref address, [], heap, heap.length, (keep.result heap address).finishes, typed⟩

theorem keep.«Supported» (heap : Mutable.Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasContainerType heap (.ref address) strings) :
    (HeapCalls.call program "keep" [.ref address] heap).Supported :=
  (keep.«Returns» heap address valid typed).supported

end tests.py.variadic_tuples
