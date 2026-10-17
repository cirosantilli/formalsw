import «.formalsw».tests.py.«maximum.py.ast»
import FormalSW

namespace tests.py.maximum
open FormalSW.PyAst

theorem maximum.result (a b : Int) :
    Calls.ReturnsValue MaximumAst.module "maximum" [.int a, .int b] (.int (max a b)) := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  apply Calls.Evaluates.builtin (.cons (Calls.Evaluates.lookup rfl) (.cons (Calls.Evaluates.lookup rfl) .nil))
  simp [Calls.Primitive.apply, Calls.positionalMaximum, Calls.maximumFrom, scalarCompare, evalCmpOp]
  split <;> simp_all [Int.max_def] <;> omega

theorem maximum.«Returns» (a b : Int) :
    (Calls.function MaximumAst.module "maximum" [.int a, .int b]).Returns :=
  (maximum.result a b).returns

end tests.py.maximum
