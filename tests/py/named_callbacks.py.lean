import «.formalsw».tests.py.«named_callbacks.py.ast»
import lang.py.FormalSW.Calls

namespace tests.py.named_callbacks
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := NamedCallbacksAst.module

private theorem increment_result (n : Int) : ReturnsValue program "increment" [.int n] (.int (n+1)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl

/-- The protected specialization retains both original callback invocations. -/
private theorem specialized_result (n : Int) :
    ReturnsValue program "__formalsw_callback_apply_twice_callback_increment" [.int n] (.int ((n+1)+1)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.call (.cons
    (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (increment_result n)) .nil)
    (increment_result (n+1))

/-- Source correctness holds for every integer input, without a finite execution bound. -/
theorem twice_increment.result (n : Int) : ReturnsValue program "twice_increment" [.int n] (.int ((n+1)+1)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (specialized_result n)

theorem twice_increment.«Returns» (n : Int) : (Calls.function program "twice_increment" [.int n]).Returns :=
  (twice_increment.result n).returns

theorem twice_increment.«ReturnType» (n : Int) : (Calls.function program "twice_increment" [.int n]).ReturnType "int" :=
  .inr ⟨_, (twice_increment.result n).finishes, rfl⟩

theorem twice_increment.«Supported» (n : Int) : (Calls.function program "twice_increment" [.int n]).Supported :=
  (twice_increment.«Returns» n).supported

end tests.py.named_callbacks
