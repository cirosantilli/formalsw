import «.formalsw».tests.py.«heap_global_context.py.ast»
import FormalSW

namespace tests.py.heap_global_context
open FormalSW.PyAst

def program : Module := HeapGlobalContextAst.module

theorem read.result (heap : Mutable.Heap) (globals : Mutable.Globals) (key : Int)
    (table : Nat) (entries : List (Constant × Mutable.Value))
    (bound : globals.lookup "TABLE" = some (.ref table))
    (found : heap[table]? = some (.dict entries)) :
    HeapCalls.ReturnsValue program "read" [.scalar (.int key)] heap
      ((ScalarDict.lookup entries (.int key)).getD (.scalar (.int 0))) heap globals := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.dictionary_get (entries := entries)
    (values := [.scalar (.int key), .scalar (.int 0)])
  · intro name same
    cases same
    cases globals with
    | nil => simp at bound
    | cons entry rest =>
        change ((entry :: rest).lookup "TABLE") ≠ none
        simp [bound]
  · apply HeapCalls.Evaluates.lookup
    cases globals with
    | nil => simp at bound
    | cons entry rest => exact bound
  · exact found
  · refine .cons (HeapCalls.Evaluates.lookup ?_) (.cons .constant .nil)
    cases globals <;> rfl
  · exact Mutable.dictionaryGet_scalar heap table entries found (.int key) (.scalar (.int 0))

theorem forward.result (heap : Mutable.Heap) (globals : Mutable.Globals) (key : Int)
    (table : Nat) (entries : List (Constant × Mutable.Value))
    (bound : globals.lookup "TABLE" = some (.ref table))
    (found : heap[table]? = some (.dict entries)) :
    HeapCalls.ReturnsValue program "forward" [.scalar (.int key)] heap
      ((ScalarDict.lookup entries (.int key)).getD (.scalar (.int 0))) heap globals := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.call (values := [.scalar (.int key)]) (middle := heap)
  · refine .cons (HeapCalls.Evaluates.lookup ?_) .nil
    cases globals <;> rfl
  · exact read.result heap globals key table entries bound found

theorem update.result (heap : Mutable.Heap) (globals : Mutable.Globals) (key value : Int)
    (table : Nat) (entries : List (Constant × Mutable.Value))
    (bound : globals.lookup "TABLE" = some (.ref table))
    (found : heap[table]? = some (.dict entries)) :
    HeapCalls.ReturnsValue program "update" [.scalar (.int key), .scalar (.int value)] heap
      (.scalar (.int value))
      (heap.set table (.dict (ScalarDict.insert entries (.int key) (.scalar (.int value))))) globals := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.setItem (index := .name "key")
    (receiver := .ref table) (subscript := .scalar (.int key))
    (value := .scalar (.int value)) (afterRhs := heap) (afterTarget := heap)
    (afterWrite := heap.set table (.dict (ScalarDict.insert entries (.int key) (.scalar (.int value)))))
    (by intro a b c h; cases h)
  · apply HeapCalls.Evaluates.lookup
    cases globals <;> rfl
  · refine .cons (HeapCalls.Evaluates.lookup ?_) (.cons (HeapCalls.Evaluates.lookup ?_) .nil)
    · cases globals with
      | nil => simp at bound
      | cons entry rest =>
          simpa [HeapCalls.functionEnv, blockLocals, assignedLocals, targetLocals] using bound
    · cases globals <;> rfl
  · exact Mutable.setItem_dictionary heap table entries found (.int key) (.scalar (.int value))
  · apply HeapCalls.BlockReturns.return_value
    apply HeapCalls.Evaluates.call (values := [.scalar (.int key)])
    · refine .cons (HeapCalls.Evaluates.lookup ?_) .nil
      cases globals <;> rfl
    · have inside : table < heap.length := by
        by_cases inside : table < heap.length
        · exact inside
        · simp [List.getElem?_eq_none (show heap.length ≤ table by omega)] at found
      simpa [ScalarDict.lookup_insert_self] using
        read.result (heap.set table (.dict (ScalarDict.insert entries (.int key) (.scalar (.int value)))))
          globals key table (ScalarDict.insert entries (.int key) (.scalar (.int value))) bound (by simp [inside])

end tests.py.heap_global_context
