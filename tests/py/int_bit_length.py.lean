import «.formalsw».tests.py.«int_bit_length.py.ast»
import FormalSW

namespace tests.py.int_bit_length
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := IntBitLengthAst.module

theorem bits.«Returns» (n : Int) : (function program "bits" [.int n]).Returns := by
  apply ReturnsValue.returns (value := .int (FormalSW.Py.Builtin.Int.bitLength n))
  apply BlockReturns.function rfl rfl
  exact BlockReturns.return_value (Evaluates.builtin (.cons (Evaluates.lookup rfl) .nil) rfl)

theorem missing.throws (s : String) : (function program "missing" [.string s]).Throws := by
  refine ⟨{ typeName := "AttributeError", args := [] }, ?_⟩
  exact Execution.finishes_of_observe (fuel := 30) rfl

theorem receiver_error.throws (n : Int) : (function program "receiver_error" [.int n]).Throws := by
  refine ⟨{ typeName := "ZeroDivisionError", args := [] }, ?_⟩
  exact Execution.finishes_of_observe (fuel := 30) rfl

end tests.py.int_bit_length
