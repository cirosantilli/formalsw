import «.formalsw».tests.py.«decimal_roundtrip.py.ast»
import FormalSW

namespace tests.py.decimal_roundtrip
open FormalSW.PyAst
private abbrev program := DecimalRoundtripAst.module

/-- The actual source returns its input for every integer, with no digit limit. -/
theorem roundtrip.result (n : Int) :
    Calls.ReturnsValue program "roundtrip" [.int n] (.int n) := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  apply Calls.Evaluates.builtin (values := [.string (toString n)])
  · exact .cons (Calls.Evaluates.builtin (.cons (Calls.Evaluates.lookup rfl) .nil) rfl) .nil
  · exact Calls.integerConversion_int n

theorem roundtrip.«Returns» (n : Int) :
    (Calls.function program "roundtrip" [.int n]).Returns :=
  (roundtrip.result n).returns

theorem roundtrip.«Supported» (n : Int) :
    (Calls.function program "roundtrip" [.int n]).Supported :=
  (roundtrip.«Returns» n).supported

end tests.py.decimal_roundtrip
