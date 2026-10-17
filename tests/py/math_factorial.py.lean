import «.formalsw».tests.py.«math_factorial.py.ast»
import FormalSW

namespace tests.py.math_factorial
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := MathFactorialAst.module

theorem fact.result (n : Nat) :
    ReturnsValue program "fact" [.int n] (.int (Math.factorial n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.library_call (.cons (Evaluates.lookup rfl) .nil) rfl
  exact congrArg some (Math.factorialCall_natural n)

theorem qualified.result (n : Nat) :
    ReturnsValue program "qualified" [.int n] (.int (Math.factorial n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.qualified_call
  apply Evaluates.library_call (.cons (Evaluates.lookup rfl) .nil) rfl
  exact congrArg some (Math.factorialCall_natural n)

theorem fact.«Returns» (n : Int)
    (condition : Condition program (fun name => if name = "n" then some (.int n) else none)
      MathFactorialAst.requires_fact_0) : (function program "fact" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Evaluates.condition_int_compare condition rfl
  simpa [Int.toNat_of_nonneg nonnegative] using (fact.result n.toNat).returns

theorem qualified.«Equiv(fact)» (n : Int)
    (condition : Condition program (fun name => if name = "n" then some (.int n) else none)
      MathFactorialAst.requires_qualified_0) :
    (function program "qualified" [.int n]).Equiv (function program "fact" [.int n]) := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Evaluates.condition_int_compare condition rfl
  simpa [Int.toNat_of_nonneg nonnegative] using
    (qualified.result n.toNat).equiv (fact.result n.toNat)

end tests.py.math_factorial
