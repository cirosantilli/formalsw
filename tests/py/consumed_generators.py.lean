import «.formalsw».tests.py.«consumed_generators.py.ast»
import lang.py.FormalSW.GeneratorCalls

namespace tests.py.consumed_generators
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := ConsumedGeneratorsAst.module

theorem eager.result (heap : Heap) (address : Nat) (items : List Mutable.Value)
    (found : heap[address]? = some (.list items)) :
    ReturnsValue program "eager" [.ref address] heap (.ref heap.length) (heap ++ [.list items]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.builtin (.cons (Evaluates.lookup rfl) .nil) (primitive_list_list heap address items found)

theorem copied.result (heap : Heap) (address : Nat) (items : List Mutable.Value)
    (found : heap[address]? = some (.list items)) :
    ReturnsValue program "copied" [.ref address] heap (.ref heap.length) (heap ++ [.list items]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.consume_generator_list
  exact GeneratorCollects.copy_sequence rfl found ⟨rfl, rfl⟩

theorem eager.«Returns» (heap : Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "eager" [.ref address] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (eager.result heap address _ found).returns

theorem eager.«Supported» (heap : Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "eager" [.ref address] heap).Supported :=
  (eager.«Returns» heap address valid typed).supported

theorem copied.«Equiv(eager)» (heap : Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "copied" [.ref address] heap).Equiv
      (HeapCalls.call program "eager" [.ref address] heap) := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact Mutable.Call.equiv_of_finishes (copied.result heap address _ found).finishes
    (eager.result heap address _ found).finishes (.inl rfl)

theorem copied.«Supported» :
    (∀ heap address, heap.Valid → Mutable.Value.HasType heap (.ref address) "list[int]" →
      (HeapCalls.call program "copied" [.ref address] heap).Supported) ∧
    (∀ heap address, heap.Valid → Mutable.Value.HasType heap (.ref address) "list[int]" →
      (HeapCalls.call program "eager" [.ref address] heap).Supported) := by
  constructor
  · intro heap address _ typed
    obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
    exact (copied.result heap address _ found).returns.supported
  · exact eager.«Supported»

theorem ordered.result (heap : Heap) (address : Nat) (items : List Int)
    (found : heap[address]? = some (.list (items.map fun n => .scalar (.int n)))) :
    ReturnsValue program "ordered" [.ref address] heap (.ref (heap.length + 1))
      (heap ++ [.list (items.map fun n => .scalar (.int n)),
        .list ((ScalarSort.ints items).map fun n => .scalar (.int n))]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.consume_generator_sorted
  apply GeneratorCollects.copy_sequence rfl found
  have sorted := primitive_sorted_list (heap ++ [.list (items.map fun n => .scalar (.int n))]) heap.length
      (items.map Constant.int) ((ScalarSort.ints items).map Constant.int)
      (by simp [List.map_map, Function.comp_def]) (ScalarSort.sort_ints items)
  change primitive (.builtin .sorted) [.ref heap.length] _ = _
  simpa only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
    List.map_map, Function.comp_def, List.append_assoc, List.cons_append, List.nil_append] using sorted

theorem ordered.«Returns» (heap : Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "ordered" [.ref address] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (ordered.result heap address items found).returns

theorem ordered.«Supported» (heap : Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "ordered" [.ref address] heap).Supported :=
  (ordered.«Returns» heap address valid typed).supported

theorem joined.result (heap : Heap) (address : Nat) (items : List String)
    (found : heap[address]? = some (.list (items.map fun s => .scalar (.string s)))) :
    ReturnsValue program "joined" [.ref address] heap (.scalar (.string (String.intercalate "" items)))
      (heap ++ [.list (items.map fun s => .scalar (.string s))]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.consume_generator_join Evaluates.constant
  apply GeneratorCollects.copy_sequence rfl found
  exact primitive_join_list _ heap.length "" items (by simp)

theorem joined.«Returns» (heap : Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[str]") :
    (HeapCalls.call program "joined" [.ref address] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.strings_of_hasType typed
  exact (joined.result heap address items found).returns

theorem joined.«Supported» (heap : Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[str]") :
    (HeapCalls.call program "joined" [.ref address] heap).Supported :=
  (joined.«Returns» heap address valid typed).supported

end tests.py.consumed_generators
