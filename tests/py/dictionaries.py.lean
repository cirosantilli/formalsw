import «.formalsw».tests.py.«dictionaries.py.ast»
import FormalSW

namespace tests.py.dictionaries
open FormalSW.PyAst
private abbrev program := DictionariesAst.module

private def table (n key : Int) : List (Constant × Mutable.Value) :=
  ScalarDict.insert [(.bool true, .scalar (.int 0))] (.int key) (.scalar (.int n))

/-- Arbitrary keys include the True/1 collision; both names share one dictionary. -/
theorem roundtrip.result (n key : Int) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "roundtrip" [.scalar (.int n), .scalar (.int key)] heap
      (.scalar (.int n))
      ((heap ++ [Mutable.Object.dict (table n key)]).set heap.length
        (Mutable.Object.dict (ScalarDict.insert (table n key) (.int key) (.scalar (.int (n + 1)))))) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.assign
  · apply HeapCalls.Evaluates.dictionary
    exact .cons HeapCalls.Evaluates.constant HeapCalls.Evaluates.constant
      (.cons (HeapCalls.Evaluates.lookup rfl) (HeapCalls.Evaluates.lookup rfl) .nil)
  · apply HeapCalls.BlockReturns.assign (HeapCalls.Evaluates.lookup rfl)
    apply HeapCalls.BlockReturns.setItem (by intros; simp)
      (HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup rfl) HeapCalls.Evaluates.constant rfl)
      (.cons (HeapCalls.Evaluates.lookup rfl) (.cons (HeapCalls.Evaluates.lookup rfl) .nil))
    · apply Mutable.setItem_dictionary (entries := table n key)
      simp [table, ScalarDict.insert]
    · apply HeapCalls.BlockReturns.return_value
      apply HeapCalls.Evaluates.binary (av := .scalar (.int (n + 1)))
      · apply HeapCalls.Evaluates.dictionary_get
          (entries := ScalarDict.insert (table n key) (.int key) (.scalar (.int (n + 1))))
          (by intro name equal; cases equal; simp [HeapCalls.setLocal])
          (HeapCalls.Evaluates.lookup rfl)
        · simp
        · exact .cons (HeapCalls.Evaluates.lookup rfl) (.cons HeapCalls.Evaluates.constant .nil)
        · change Mutable.dictionaryGet _ _ _ _ = _
          rw [Mutable.dictionaryGet_scalar _ _
            (ScalarDict.insert (table n key) (.int key) (.scalar (.int (n + 1))))
            (by simp), ScalarDict.lookup_insert_self]
          rfl
      · exact HeapCalls.Evaluates.constant
      · simp [Mutable.binary, scalarBinary]

private theorem reference.result (n key : Int) :
    Finishes (scalarFunction program "reference" [.int n, .int key]).step
      (scalarFunction program "reference" [.int n, .int key]).initial (.ok (.int n)) :=
  Execution.finishes_of_observe (fuel := 2) rfl

theorem roundtrip.«Returns» (n key : Int) :
    (HeapCalls.scalarFunction program "roundtrip" [.int n, .int key]).Returns :=
  (roundtrip.result n key []).scalar_returns

theorem roundtrip.«Equiv(reference)» (n key : Int) :
    (HeapCalls.scalarFunction program "roundtrip" [.int n, .int key]).Equiv
      (scalarFunction program "reference" [.int n, .int key]) := by
  have left := HeapCalls.ReturnsValue.scalar_finishes (values := [.int n, .int key])
    (roundtrip.result n key [])
  have right := reference.result n key
  intro outcome
  constructor
  · intro run
    rw [run.unique left]
    exact right
  · intro run
    rw [run.unique right]
    exact left

theorem roundtrip.«Supported» :
    (∀ n key : Int, (HeapCalls.scalarFunction program "roundtrip" [.int n, .int key]).Supported) ∧
    (∀ n key : Int, (scalarFunction program "reference" [.int n, .int key]).Supported) :=
  ⟨fun n key => (roundtrip.«Returns» n key).supported,
    fun n key => Execution.supported_of_finishes (reference.result n key)⟩

end tests.py.dictionaries
