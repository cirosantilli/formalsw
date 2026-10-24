import «.formalsw».tests.py.«bitwise_and.py.ast»
import FormalSW

namespace tests.py.bitwise_and
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := BitwiseAndAst.module

theorem mask.result (a b : Int) :
    ReturnsValue program "mask" [.int a, .int b] (.int (integerBitAnd a b)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl)
    (by simp [scalarBinary, scalarBitAnd])

theorem mask.«Returns» (a b : Int) : (function program "mask" [.int a, .int b]).Returns :=
  (mask.result a b).returns

theorem both.result (a b : Bool) :
    ReturnsValue program "both" [.bool a, .bool b] (.bool (a && b)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl) rfl

theorem both.«Returns» (a b : Bool) : (function program "both" [.bool a, .bool b]).Returns :=
  (both.result a b).returns

end tests.py.bitwise_and
