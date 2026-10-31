import «.formalsw».tests.py.«tuple_memo_keys.py.ast»
import lang.py.FormalSW.HeapMemoCallRules

/-! Equal tuples reuse the cached object, including freshly allocated nested tuples. -/
namespace tests.py.tuple_memo_keys
open FormalSW.PyAst
private abbrev program := TupleMemoKeysAst.module


/-- Equal immutable values have one key even when their tuple references differ. -/
theorem tuple_keys_by_value (heap : Mutable.Heap) (name : String) (n : Int)
    (left right : Nat) (items : List Int)
    (leftFound : heap[left]? =
      some (.tuple (items.map (fun item => Mutable.Value.scalar (.int item)))))
    (rightFound : heap[right]? =
      some (.tuple (items.map (fun item => Mutable.Value.scalar (.int item))))) :
    HeapMemoCalls.memoKey heap name [.scalar (.int n), .ref left] =
      HeapMemoCalls.memoKey heap name [.scalar (.int n), .ref right] := by
  rw [HeapMemoCalls.memoKey_integer_tuple _ _ _ _ _ leftFound,
    HeapMemoCalls.memoKey_integer_tuple _ _ _ _ _ rightFound]

theorem tuple_and_integer_keys_differ (name : String) (values : List Int) (items : List HashKey) :
    (⟨name, [], some items⟩ : MemoCalls.Key) ≠ ⟨name, values, none⟩ := by
  intro same
  have impossible := congrArg MemoCalls.Key.structuredArguments same
  cases impossible

private theorem scenario_result :
    Finishes (HeapMemoCalls.scalarFunction program "scenario" []).step
      (HeapMemoCalls.scalarFunction program "scenario" []).initial (.ok (.bool true)) :=
  Execution.finishes_of_observe (fuel := 500) rfl

private theorem nested_result :
    Finishes (HeapMemoCalls.scalarFunction program "nested_scenario" []).step
      (HeapMemoCalls.scalarFunction program "nested_scenario" []).initial (.ok (.bool true)) :=
  Execution.finishes_of_observe (fuel := 500) rfl

theorem scenario.«Returns» : (HeapMemoCalls.scalarFunction program "scenario" []).Returns :=
  ⟨_, scenario_result⟩

theorem scenario.«Supported» : (HeapMemoCalls.scalarFunction program "scenario" []).Supported :=
  scenario.«Returns».supported

theorem nested_scenario.«Returns» :
    (HeapMemoCalls.scalarFunction program "nested_scenario" []).Returns := ⟨_, nested_result⟩

theorem nested_scenario.«Supported» :
    (HeapMemoCalls.scalarFunction program "nested_scenario" []).Supported :=
  nested_scenario.«Returns».supported

private theorem generator_result :
    Finishes (HeapMemoCalls.scalarFunction program "generator_scenario" []).step
      (HeapMemoCalls.scalarFunction program "generator_scenario" []).initial (.ok (.bool true)) :=
  Execution.finishes_of_observe (fuel := 500) rfl

theorem generator_scenario.«Returns» :
    (HeapMemoCalls.scalarFunction program "generator_scenario" []).Returns := ⟨_, generator_result⟩

theorem generator_scenario.«Supported» :
    (HeapMemoCalls.scalarFunction program "generator_scenario" []).Supported :=
  generator_scenario.«Returns».supported

end tests.py.tuple_memo_keys
