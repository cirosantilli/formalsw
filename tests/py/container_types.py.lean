import «.formalsw».tests.py.«container_types.py.ast»
import lang.py.FormalSW.ContainerTypes
import FormalSW

namespace tests.py.container_types
open FormalSW.PyAst
private abbrev program := ContainerTypesAst.module
private abbrev pairs : Mutable.ContainerType := .list (.tuple [.scalar "int", .scalar "int"])

theorem keep_pairs.result (heap : Mutable.Heap) (address : Nat) :
    HeapCalls.ReturnsValue program "keep_pairs" [.ref address] heap (.ref address) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup rfl)

theorem keep_pairs.«Returns» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (_typed : Mutable.Value.HasContainerType heap (.ref address) pairs) :
    (HeapCalls.call program "keep_pairs" [.ref address] heap).Returns :=
  (keep_pairs.result heap address).returns

theorem keep_pairs.«ReturnType» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasContainerType heap (.ref address) pairs) :
    (HeapCalls.call program "keep_pairs" [.ref address] heap).ReturnContainerType pairs :=
  .inr ⟨.ref address, [], heap, heap.length, (keep_pairs.result heap address).finishes, typed⟩

theorem keep_pairs.«Supported» (heap : Mutable.Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasContainerType heap (.ref address) pairs) :
    (HeapCalls.call program "keep_pairs" [.ref address] heap).Supported :=
  (keep_pairs.«Returns» heap address valid typed).supported

/-- The two list entries can refer to the very same immutable tuple. -/
example : Mutable.Value.HasContainerType
    [.list [.ref 1, .ref 1], .tuple [.scalar (.int 2), .scalar (.int 3)]] (.ref 0) pairs := by
  have row : Mutable.Value.HasContainerType
      [.list [.ref 1, .ref 1], .tuple [.scalar (.int 2), .scalar (.int 3)]] (.ref 1)
      (.tuple [.scalar "int", .scalar "int"]) := by
    refine .fixedTuple rfl rfl ?_
    intro pair member
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .scalar rfl
  refine .list rfl ?_
  intro item member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact row

example : ¬ Mutable.Value.HasContainerType [.list []] (.ref 0) (.tuple []) := by
  intro typed
  obtain ⟨items, impossible, _⟩ := Mutable.Value.hasContainerType_tuple_iff.mp typed
  cases impossible

example : ¬ Mutable.Value.HasContainerType [] (.scalar (.bool true)) (.scalar "int") := by
  intro typed
  obtain ⟨n, impossible⟩ := Mutable.Value.hasContainerType_int_iff.mp typed
  cases impossible

end tests.py.container_types
