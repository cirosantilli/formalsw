import «.formalsw».tests.py.«list_extend.py.ast»
import lang.py.FormalSW.ListExtensionCalls

namespace tests.py.list_extend
open FormalSW.PyAst HeapCalls
private abbrev program := ListExtendAst.module

/-- The two input references may alias, and their elements can themselves be shared. -/
theorem extend.result (heap : Mutable.Heap) (address source : Nat) (items extra : List Mutable.Value)
    (destination : heap[address]? = some (.list items)) (input : heap[source]? = some (.list extra)) :
    ReturnsValue program "extend" [.ref address, .ref source] heap (.scalar .none)
      (heap.set address (.list (items ++ extra))) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.discard
    (Evaluates.extendList (Evaluates.lookup rfl) destination (.cons (Evaluates.lookup rfl) .nil)
      (extendList_list heap address source items extra destination input)
      (by intro name same; cases same; rfl))
  exact fun _ _ => .next rfl .refl

theorem extend.«Returns» (heap : Mutable.Heap) (address source : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]")
    (sourceTyped : Mutable.Value.HasType heap (.ref source) "list[int]") :
    (HeapCalls.call program "extend" [.ref address, .ref source] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  obtain ⟨extra, input⟩ := Mutable.Value.ints_of_hasType sourceTyped
  exact (extend.result heap address source _ _ found input).returns

theorem extend.«ReturnType» (heap : Mutable.Heap) (address source : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]")
    (sourceTyped : Mutable.Value.HasType heap (.ref source) "list[int]") :
    (HeapCalls.call program "extend" [.ref address, .ref source] heap).ReturnType "None" := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  obtain ⟨extra, input⟩ := Mutable.Value.ints_of_hasType sourceTyped
  exact .inr ⟨_, [], _, heap.length, (extend.result heap address source _ _ found input).finishes, rfl⟩

theorem extend.«Supported» (heap : Mutable.Heap) (address source : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]")
    (sourceTyped : Mutable.Value.HasType heap (.ref source) "list[int]") :
    (HeapCalls.call program "extend" [.ref address, .ref source] heap).Supported :=
  (extend.«Returns» heap address source valid typed sourceTyped).supported

end tests.py.list_extend
