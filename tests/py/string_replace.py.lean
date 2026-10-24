import «.formalsw».tests.py.«string_replace.py.ast»
import lang.py.FormalSW.HeapCalls

namespace tests.py.string_replace
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := StringReplaceAst.module

theorem replace.result (heap : Mutable.Heap) (text old new : String) (count : Int) :
    ReturnsValue program "replace"
      [.scalar (.string text), .scalar (.string old), .scalar (.string new), .scalar (.int count)] heap
      (.scalar (.string (Strings.replace text old new count))) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.replace (Evaluates.lookup rfl)
    (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)))
  · rfl
  · intro name equal
    cases equal
    rfl

private abbrev conditionEnv (count : Int) : ScalarEnv :=
  fun name => if name = "count" then some (.int count) else none

theorem replace.«Returns» (text old new : String) (count : Int)
    (_condition : Calls.Condition program (conditionEnv count) StringReplaceAst.requires_replace_0) :
    (HeapCalls.scalarFunction program "replace" [.string text, .string old, .string new, .int count]).Returns :=
  (replace.result [] text old new count).scalar_returns

theorem replace.«Supported» (text old new : String) (count : Int)
    (condition : Calls.Condition program (conditionEnv count) StringReplaceAst.requires_replace_0) :
    (HeapCalls.scalarFunction program "replace" [.string text, .string old, .string new, .int count]).Supported :=
  (replace.«Returns» text old new count condition).supported

theorem replace_all.result (heap : Mutable.Heap) (text old new : String) :
    ReturnsValue program "replace_all"
      [.scalar (.string text), .scalar (.string old), .scalar (.string new)] heap
      (.scalar (.string (Strings.replace text old new))) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.replace (Evaluates.lookup rfl)
    (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil))
  · rfl
  · intro name equal
    cases equal
    rfl

theorem replace_all.«Returns» (text old new : String) :
    (HeapCalls.scalarFunction program "replace_all" [.string text, .string old, .string new]).Returns :=
  (replace_all.result [] text old new).scalar_returns

theorem replace_all.«Supported» (text old new : String) :
    (HeapCalls.scalarFunction program "replace_all" [.string text, .string old, .string new]).Supported :=
  (replace_all.«Returns» text old new).supported

end tests.py.string_replace
