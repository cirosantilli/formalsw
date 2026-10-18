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

private abbrev context (table : Nat) : Mutable.Globals := [("TABLE", .ref table)]
private abbrev prerequisite (heap : Mutable.Heap) (table : Nat) :=
  HeapCalls.Condition program (fun name => (context table).lookup name) HeapGlobalContextAst.requires_forward_0 heap (context table)

theorem read.«Returns» (heap : Mutable.Heap) (key : Int) (table : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref table) "dict[int,int]") :
    (HeapCalls.call program "read" [.scalar (.int key)] heap (context table)).Returns := by
  obtain ⟨entries, found, _⟩ := Mutable.Value.dictionary_of_hasType typed rfl
  exact (read.result heap (context table) key table entries rfl found).returns

theorem read.«Supported» (heap : Mutable.Heap) (key : Int) (table : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref table) "dict[int,int]") :
    (HeapCalls.call program "read" [.scalar (.int key)] heap (context table)).Supported :=
  (read.«Returns» heap key table valid typed).supported

theorem forward.«Returns» (heap : Mutable.Heap) (key : Int) (table : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref table) "dict[int,int]")
    (_requires : prerequisite heap table) :
    (HeapCalls.call program "forward" [.scalar (.int key)] heap (context table)).Returns := by
  obtain ⟨entries, found, _⟩ := Mutable.Value.dictionary_of_hasType typed rfl
  exact (forward.result heap (context table) key table entries rfl found).returns

theorem forward.«Equiv(read)» (heap : Mutable.Heap) (key : Int) (table : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref table) "dict[int,int]")
    (_requires : prerequisite heap table) :
    (HeapCalls.call program "forward" [.scalar (.int key)] heap (context table)).Equiv
      (HeapCalls.call program "read" [.scalar (.int key)] heap (context table)) := by
  obtain ⟨entries, found, _⟩ := Mutable.Value.dictionary_of_hasType typed rfl
  exact Mutable.Call.equiv_of_finishes (forward.result heap (context table) key table entries rfl found).finishes
    (read.result heap (context table) key table entries rfl found).finishes (.inl rfl)

theorem forward.«Supported» :
    (∀ heap key table, heap.Valid → Mutable.Value.HasType heap (.ref table) "dict[int,int]" →
      prerequisite heap table → (HeapCalls.call program "forward" [.scalar (.int key)] heap (context table)).Supported) ∧
    (∀ heap key table, heap.Valid → Mutable.Value.HasType heap (.ref table) "dict[int,int]" →
      prerequisite heap table → (HeapCalls.call program "read" [.scalar (.int key)] heap (context table)).Supported) :=
  ⟨fun heap key table valid typed condition => (forward.«Returns» heap key table valid typed condition).supported,
   fun heap key table valid typed _ => (read.«Returns» heap key table valid typed).supported⟩

theorem update.«Returns» (heap : Mutable.Heap) (key value : Int) (table : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref table) "dict[int,int]") :
    (HeapCalls.call program "update" [.scalar (.int key), .scalar (.int value)] heap (context table)).Returns := by
  obtain ⟨entries, found, _⟩ := Mutable.Value.dictionary_of_hasType typed rfl
  exact (update.result heap (context table) key value table entries rfl found).returns

theorem update.«Supported» (heap : Mutable.Heap) (key value : Int) (table : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref table) "dict[int,int]") :
    (HeapCalls.call program "update" [.scalar (.int key), .scalar (.int value)] heap (context table)).Supported :=
  (update.«Returns» heap key value table valid typed).supported

theorem requires_forward_0_supported (heap : Mutable.Heap) (_key : Int) (table : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref table) "dict[int,int]") :
    (HeapCalls.evaluate program (fun name => (context table).lookup name) HeapGlobalContextAst.requires_forward_0 heap (context table)).Supported := by
  obtain ⟨items, found, _⟩ := Mutable.Value.dictionary_of_hasType typed rfl
  have result : HeapCalls.Evaluates program (fun name => (context table).lookup name) HeapGlobalContextAst.requires_forward_0
      heap (.scalar (.bool true)) heap (context table) := by
    apply HeapCalls.Evaluates.compare (av := .scalar (.int items.length)) (middle := heap) (afterRight := heap)
    · exact HeapCalls.Evaluates.builtin (.cons (HeapCalls.Evaluates.lookup rfl) .nil)
        (by simp [HeapCalls.primitive, Mutable.length, found])
    · exact HeapCalls.Evaluates.constant
    · simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  exact Execution.supported_of_finishes result.finishes

end tests.py.heap_global_context
