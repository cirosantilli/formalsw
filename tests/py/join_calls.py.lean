import «.formalsw».tests.py.«join_calls.py.ast»
import lang.py.FormalSW.HeapCalls

namespace tests.py.join_calls
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := JoinCallsAst.module

theorem combine.result (separator : String) (heap : Mutable.Heap) (address : Nat) (items : List String)
    (found : heap[address]? = some (.list (items.map fun s => .scalar (.string s)))) :
    ReturnsValue program "combine" [.scalar (.string separator), .ref address] heap
      (.scalar (.string (String.intercalate separator items))) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.join (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)
    (primitive_join_list heap address separator items found)
  intro name equal
  cases equal
  rfl

theorem combine.«Returns» (heap : Mutable.Heap) (separator : String) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[str]") :
    (HeapCalls.call program "combine" [.scalar (.string separator), .ref address] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.strings_of_hasType typed
  exact (combine.result separator heap address items found).returns

theorem combine.«ReturnType» (heap : Mutable.Heap) (separator : String) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[str]") :
    (HeapCalls.call program "combine" [.scalar (.string separator), .ref address] heap).ReturnType "str" := by
  obtain ⟨items, found⟩ := Mutable.Value.strings_of_hasType typed
  exact .inr ⟨_, [], heap, heap.length, (combine.result separator heap address items found).finishes, rfl⟩

theorem combine.«Supported» (heap : Mutable.Heap) (separator : String) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[str]") :
    (HeapCalls.call program "combine" [.scalar (.string separator), .ref address] heap).Supported :=
  (combine.«Returns» heap separator address valid typed).supported

theorem concatenate.result (heap : Mutable.Heap) (address : Nat) (items : List String)
    (found : heap[address]? = some (.list (items.map fun s => .scalar (.string s)))) :
    ReturnsValue program "concatenate" [.ref address] heap
      (.scalar (.string (String.intercalate "" items))) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.join Evaluates.constant (.cons (Evaluates.lookup rfl) .nil)
    (primitive_join_list heap address "" items found)
  intro name equal
  cases equal

theorem concatenate.«Returns» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[str]") :
    (HeapCalls.call program "concatenate" [.ref address] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.strings_of_hasType typed
  exact (concatenate.result heap address items found).returns

theorem concatenate.«Supported» (heap : Mutable.Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[str]") :
    (HeapCalls.call program "concatenate" [.ref address] heap).Supported :=
  (concatenate.«Returns» heap address valid typed).supported

end tests.py.join_calls
