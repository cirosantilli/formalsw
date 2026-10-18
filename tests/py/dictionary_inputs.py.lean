import «.formalsw».tests.py.«dictionary_inputs.py.ast»
import FormalSW

namespace tests.py.dictionary_inputs
open FormalSW.PyAst
private abbrev program := DictionaryInputsAst.module

private theorem identity.result (heap : Mutable.Heap) (table : Nat) :
    HeapCalls.ReturnsValue program "identity" [.ref table] heap (.ref table) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup rfl)

private theorem reference.result (heap : Mutable.Heap) (table : Nat) :
    HeapCalls.ReturnsValue program "reference" [.ref table] heap (.ref table) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup rfl)

private abbrev inputEnv (table : Nat) : HeapCalls.Env :=
  fun name => if name = "table" then some (.ref table) else none

private theorem identity.condition (heap : Mutable.Heap) (table : Nat)
    (typed : Mutable.Value.HasType heap (.ref table) "dict[int,str]") :
    HeapCalls.Evaluates program (inputEnv table) DictionaryInputsAst.requires_identity_0 heap
      (.scalar (.bool true)) heap := by
  obtain ⟨items, found, _⟩ := Mutable.Value.dictionary_of_hasType typed (by rfl)
  apply HeapCalls.Evaluates.compare (av := .scalar (.int items.length)) (middle := heap) (afterRight := heap)
  · exact HeapCalls.Evaluates.builtin (.cons (HeapCalls.Evaluates.lookup rfl) .nil)
      (by simp [HeapCalls.primitive, Mutable.length, found])
  · exact HeapCalls.Evaluates.constant
  · simp [HeapCalls.compare, scalarCompare, evalCmpOp]

theorem requires_identity_0_supported (heap : Mutable.Heap) (table : Nat)
    (_valid : Mutable.Heap.Valid heap) (typed : Mutable.Value.HasType heap (.ref table) "dict[int,str]") :
    (HeapCalls.evaluate program (inputEnv table) DictionaryInputsAst.requires_identity_0 heap).Supported :=
  Execution.supported_of_finishes (identity.condition heap table typed).finishes

theorem identity.«Returns» (heap : Mutable.Heap) (table : Nat)
    (_valid : Mutable.Heap.Valid heap) (_typed : Mutable.Value.HasType heap (.ref table) "dict[int,str]")
    (_requires : HeapCalls.Condition program (inputEnv table) DictionaryInputsAst.requires_identity_0 heap) :
    (HeapCalls.call program "identity" [.ref table] heap).Returns :=
  (identity.result heap table).returns

theorem identity.«Equiv(reference)» (heap : Mutable.Heap) (table : Nat)
    (_valid : Mutable.Heap.Valid heap) (_typed : Mutable.Value.HasType heap (.ref table) "dict[int,str]")
    (_requires : HeapCalls.Condition program (inputEnv table) DictionaryInputsAst.requires_identity_0 heap) :
    (HeapCalls.call program "identity" [.ref table] heap).Equiv
      (HeapCalls.call program "reference" [.ref table] heap) :=
  Mutable.Call.equiv_of_finishes (identity.result heap table).finishes (reference.result heap table).finishes (.inl rfl)

theorem identity.«ReturnType» (heap : Mutable.Heap) (table : Nat)
    (_valid : Mutable.Heap.Valid heap) (typed : Mutable.Value.HasType heap (.ref table) "dict[int,str]")
    (_requires : HeapCalls.Condition program (inputEnv table) DictionaryInputsAst.requires_identity_0 heap) :
    (HeapCalls.call program "identity" [.ref table] heap).ReturnType "dict[int,str]" :=
  .inr ⟨.ref table, [], heap, heap.length, (identity.result heap table).finishes, typed⟩

theorem identity.«Supported» :
    (∀ (heap : Mutable.Heap) (table : Nat), Mutable.Heap.Valid heap →
      Mutable.Value.HasType heap (.ref table) "dict[int,str]" →
      HeapCalls.Condition program (inputEnv table) DictionaryInputsAst.requires_identity_0 heap →
      (HeapCalls.call program "identity" [.ref table] heap).Supported) ∧
    (∀ (heap : Mutable.Heap) (table : Nat), Mutable.Heap.Valid heap →
      Mutable.Value.HasType heap (.ref table) "dict[int,str]" →
      HeapCalls.Condition program (inputEnv table) DictionaryInputsAst.requires_identity_0 heap →
      (HeapCalls.call program "reference" [.ref table] heap).Supported) :=
  ⟨fun heap table _ _ _ => (identity.result heap table).returns.supported,
   fun heap table _ _ _ => (reference.result heap table).returns.supported⟩

private theorem lookup.result (heap : Mutable.Heap) (table : Nat) (key : Int)
    (entries : List (Constant × Mutable.Value)) (found : heap[table]? = some (.dict entries)) :
    HeapCalls.ReturnsValue program "lookup" [.ref table, .scalar (.int key)] heap
      ((ScalarDict.lookup entries (.int key)).getD (.scalar (.string ""))) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.dictionary_get
    (by intro name equal; cases equal; simp [HeapCalls.argumentEnv])
    (HeapCalls.Evaluates.lookup rfl) found
    (.cons (HeapCalls.Evaluates.lookup rfl) (.cons HeapCalls.Evaluates.constant .nil))
  exact Mutable.dictionaryGet_scalar _ _ _ found _ _

theorem lookup.«Returns» (heap : Mutable.Heap) (table : Nat) (key : Int)
    (_valid : Mutable.Heap.Valid heap) (typed : Mutable.Value.HasType heap (.ref table) "dict[int,str]") :
    (HeapCalls.call program "lookup" [.ref table, .scalar (.int key)] heap).Returns := by
  obtain ⟨entries, found, _⟩ := Mutable.Value.dictionary_of_hasType typed (by rfl)
  exact (lookup.result heap table key entries found).returns

theorem lookup.«ReturnType» (heap : Mutable.Heap) (table : Nat) (key : Int)
    (_valid : Mutable.Heap.Valid heap) (typed : Mutable.Value.HasType heap (.ref table) "dict[int,str]") :
    (HeapCalls.call program "lookup" [.ref table, .scalar (.int key)] heap).ReturnType "str" := by
  obtain ⟨entries, found, types⟩ := Mutable.Value.dictionary_of_hasType typed (by rfl)
  refine .inr ⟨_, [], heap, heap.length, (lookup.result heap table key entries found).finishes, ?_⟩
  cases selected : ScalarDict.lookup entries (.int key) with
  | none => simp [Mutable.Value.HasType]
  | some value =>
      obtain ⟨scalar, rfl, kind⟩ := ScalarDict.lookup_property entries (.int key)
        (fun value => ∃ scalar, value = .scalar scalar ∧ Mutable.scalarKind scalar = "str")
        (fun entry member => (types entry member).2) selected
      cases scalar <;> simp_all [Mutable.scalarKind, Data.typeName, Mutable.Value.HasType]

theorem lookup.«Supported» (heap : Mutable.Heap) (table : Nat) (key : Int)
    (valid : Mutable.Heap.Valid heap) (typed : Mutable.Value.HasType heap (.ref table) "dict[int,str]") :
    (HeapCalls.call program "lookup" [.ref table, .scalar (.int key)] heap).Supported :=
  (lookup.«Returns» heap table key valid typed).supported

private theorem replace.result (heap : Mutable.Heap) (table : Nat) (key : Int) (value : String)
    (entries : List (Constant × Mutable.Value)) (found : heap[table]? = some (.dict entries)) :
    HeapCalls.ReturnsValue program "replace" [.ref table, .scalar (.int key), .scalar (.string value)] heap
      (.ref table) (heap.set table (.dict (ScalarDict.insert entries (.int key) (.scalar (.string value))))) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.setItem (by intros; simp) (HeapCalls.Evaluates.lookup rfl)
    (.cons (HeapCalls.Evaluates.lookup rfl) (.cons (HeapCalls.Evaluates.lookup rfl) .nil))
    (Mutable.setItem_dictionary heap table entries found (.int key) (.scalar (.string value)))
  exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup rfl)

theorem replace.«Returns» (heap : Mutable.Heap) (table : Nat) (key : Int) (value : String)
    (_valid : Mutable.Heap.Valid heap) (typed : Mutable.Value.HasType heap (.ref table) "dict[int,str]") :
    (HeapCalls.call program "replace" [.ref table, .scalar (.int key), .scalar (.string value)] heap).Returns := by
  obtain ⟨entries, found, _⟩ := Mutable.Value.dictionary_of_hasType typed (by rfl)
  exact (replace.result heap table key value entries found).returns

theorem replace.«ReturnType» (heap : Mutable.Heap) (table : Nat) (key : Int) (value : String)
    (_valid : Mutable.Heap.Valid heap) (typed : Mutable.Value.HasType heap (.ref table) "dict[int,str]") :
    (HeapCalls.call program "replace" [.ref table, .scalar (.int key), .scalar (.string value)] heap).ReturnType "dict[int,str]" := by
  obtain ⟨entries, found, types⟩ := Mutable.Value.dictionary_of_hasType typed (by rfl)
  refine .inr ⟨.ref table, [], _, heap.length, (replace.result heap table key value entries found).finishes, ?_⟩
  have inside : table < heap.length := by
    by_cases inside : table < heap.length
    · exact inside
    · rw [List.getElem?_eq_none (by omega)] at found
      cases found
  change Mutable.Value.DictionaryHasType _ (.ref table) "int" "str"
  refine ⟨ScalarDict.insert entries (.int key) (.scalar (.string value)), ?_, ?_⟩
  · simp [inside]
  · apply ScalarDict.insert_property entries (.int key) (.scalar (.string value))
      (fun key => Mutable.scalarKind key = "int")
      (fun value => ∃ scalar, value = .scalar scalar ∧ Mutable.scalarKind scalar = "str") types rfl
    exact ⟨.string value, rfl, rfl⟩

theorem replace.«Supported» (heap : Mutable.Heap) (table : Nat) (key : Int) (value : String)
    (valid : Mutable.Heap.Valid heap) (typed : Mutable.Value.HasType heap (.ref table) "dict[int,str]") :
    (HeapCalls.call program "replace" [.ref table, .scalar (.int key), .scalar (.string value)] heap).Supported :=
  (replace.«Returns» heap table key value valid typed).supported

end tests.py.dictionary_inputs
