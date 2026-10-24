import «.formalsw».tests.py.«local_functions.py.ast»
import FormalSW

namespace tests.py.local_functions
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := LocalFunctionsAst.module

private theorem add_result (x offset : Int) :
    ReturnsValue program "__formalsw_local_shifted_add" [.int x, .int offset] (.int (x + offset)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl) rfl

/-- Captures are read at the call, after the enclosing assignment. -/
theorem shifted.«Returns» (n : Int) : (Calls.function program "shifted" [.int n]).Returns := by
  apply ReturnsValue.returns (value := .int (n + (n + 1)))
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (Evaluates.lookup rfl)
  apply BlockReturns.augAssign (value := .int (n + 1))
  · exact Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl
  · apply BlockReturns.return_value
    exact Evaluates.call (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)) (add_result n (n + 1))

end tests.py.local_functions
