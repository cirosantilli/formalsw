import «.formalsw».tests.py.«minimum.py.ast»
import FormalSW

namespace tests.py.minimum
open FormalSW.PyAst

theorem minimum.result (a b : Int) :
    Calls.ReturnsValue MinimumAst.module "minimum" [.int a, .int b] (.int (min a b)) := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  apply Calls.Evaluates.builtin (.cons (Calls.Evaluates.lookup rfl) (.cons (Calls.Evaluates.lookup rfl) .nil))
  simp [Calls.Primitive.apply, Calls.positionalMinimum, Calls.minimumFrom, scalarCompare, evalCmpOp]
  split <;> simp_all [Int.min_def] <;> omega

theorem minimum.«Returns» (a b : Int) :
    (Calls.function MinimumAst.module "minimum" [.int a, .int b]).Returns :=
  (minimum.result a b).returns

end tests.py.minimum
