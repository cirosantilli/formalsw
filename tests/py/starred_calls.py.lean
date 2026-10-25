import «.formalsw».tests.py.«starred_calls.py.ast»
import lang.py.FormalSW.HeapCalls

namespace tests.py.starred_calls
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := StarredCallsAst.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)

private theorem add_result (a b : Int) (heap : Heap) :
    ReturnsValue program "add" [number a, number b] heap (number (a+b)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl) rfl

theorem expanded.result (a b : Int) (heap : Heap) :
    ReturnsValue program "expanded" [number a, number b] heap (number (a+b))
      (heap ++ [.tuple [number a, number b]]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.call_star
    (.star (Evaluates.tuple (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)) (by simp))
      (starItems_tuple _ heap.length [number a, number b] (by simp)) .nil)
  exact add_result a b _

theorem omitted.result (a : Int) (heap : Heap) :
    ReturnsValue program "omitted" [number a] heap (number (a+7)) (heap ++ [.list [number a]]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.call_star
    (.star (Evaluates.list (.cons (Evaluates.lookup rfl) .nil))
      (starItems_list _ heap.length [number a] (by simp)) .nil)
  exact ReturnsValue.with_defaults rfl rfl rfl (add_result a 7 _)

theorem expanded.«Returns» (a b : Int) :
    (HeapCalls.scalarFunction program "expanded" [.int a, .int b]).Returns := (expanded.result a b []).scalar_returns

theorem omitted.«Returns» (a : Int) :
    (HeapCalls.scalarFunction program "omitted" [.int a]).Returns := (omitted.result a []).scalar_returns

theorem expanded.«Supported» (a b : Int) :
    (HeapCalls.scalarFunction program "expanded" [.int a, .int b]).Supported := (expanded.«Returns» a b).supported

theorem omitted.«Supported» (a : Int) :
    (HeapCalls.scalarFunction program "omitted" [.int a]).Supported := (omitted.«Returns» a).supported

end tests.py.starred_calls
