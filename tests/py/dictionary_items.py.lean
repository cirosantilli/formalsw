import «.formalsw».tests.py.«dictionary_items.py.ast»
import FormalSW

namespace tests.py.dictionary_items
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := DictionaryItemsAst.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)

/-- Arbitrary integer keys and values pass through the freshly allocated item pair. -/
theorem first_value.result (key value : Int) (heap : Mutable.Heap) :
    ReturnsValue program "first_value" [number key,number value] heap (number value)
      (heap++[.dict [(.int key,number value)]]++[.tuple [number key,number value]]) := by
  let table := heap++[Mutable.Object.dict [(.int key,number value)]]
  let final := table++[Mutable.Object.tuple [number key,number value]]
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (value := .ref heap.length) (middle := table)
  · apply Evaluates.dictionary
    exact .cons (Evaluates.lookup rfl) (Evaluates.lookup rfl) .nil
  · apply BlockReturns.for_dictionary_items (address := heap.length)
      (object := .dict [(.int key,number value)])
      (entries := [(number key,number value)]) (middle := table) (Evaluates.lookup rfl) (by simp [table]) rfl
    apply BlockReturns.dictionary_items_step (key := number key) (value := number value) (middle := table)
      (pair := .ref table.length) (afterTuple := final)
    · simpa only [List.getElem?_cons_zero] using
        dictionaryItemsNext_dict (heap := table) (address := heap.length) (position := 0)
          (entries := [(.int key,number value)]) (by simp [table])
    · simp [Mutable.allocateTuple, final, Except.map]
    · apply BlockReturns.unpack (names := ["_","item"]) (items := [number key,number value])
        (afterUnpack := final) rfl (Evaluates.lookup rfl)
        (by simp [Mutable.sequence, final]) rfl
      exact BlockReturns.return_value (Evaluates.lookup rfl)

theorem first_value.«Returns» (key value : Int) :
    (HeapCalls.scalarFunction program "first_value" [.int key,.int value]).Returns :=
  (first_value.result key value []).scalar_returns

theorem first_value.«Supported» (key value : Int) :
    (HeapCalls.scalarFunction program "first_value" [.int key,.int value]).Supported :=
  (first_value.«Returns» key value).supported

end tests.py.dictionary_items
