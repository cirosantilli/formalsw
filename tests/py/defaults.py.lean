import «.formalsw».tests.py.«defaults.py.ast»
import FormalSW

namespace tests.py.defaults
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := DefaultsAst.module

private theorem offset.result (n step : Int) :
    ReturnsValue program "offset" [.int n, .int step] (.int (n + step)) := by
  apply BlockReturns.function rfl rfl
  exact BlockReturns.return_value (Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl) rfl)

theorem offset.«Returns» (n step : Int) :
    (Calls.function program "offset" [.int n, .int step]).Returns :=
  (offset.result n step).returns

private theorem offset.default (n : Int) :
    ReturnsValue program "offset" [.int n] (.int (n + 10)) := by
  apply BlockReturns.function_defaults rfl (by simp) rfl
  exact BlockReturns.return_value (Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl) rfl)

private theorem shifted.result (n : Int) :
    ReturnsValue program "shifted" [.int n] (.int (n + 10)) := by
  apply BlockReturns.function rfl rfl
  exact BlockReturns.return_value (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (offset.default n))

private theorem reference.run (n : Int) : Finishes (scalarFunction program "reference" [.int n]).step
    (scalarFunction program "reference" [.int n]).initial (.ok (.int (n + 10))) :=
  Execution.finishes_of_observe (fuel := 5) rfl

theorem shifted.«Equiv(reference)» (n : Int) :
    (Calls.function program "shifted" [.int n]).Equiv (scalarFunction program "reference" [.int n]) := by
  intro outcome
  constructor
  · intro run
    rw [run.unique (shifted.result n).finishes]
    exact reference.run n
  · intro run
    rw [run.unique (reference.run n)]
    exact (shifted.result n).finishes

theorem combined.«Returns» (n : Int) :
    (Calls.function program "combined" [.int n]).Returns := by
  apply ReturnsValue.returns (value := .int ((n + 2) + (n + 10)))
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary
  · exact Evaluates.call (.cons (Evaluates.lookup rfl) (.cons Evaluates.constant .nil)) (offset.result n 2)
  · exact Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (offset.default n)
  · rfl

end tests.py.defaults
