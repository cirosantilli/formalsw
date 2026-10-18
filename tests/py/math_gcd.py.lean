import «.formalsw».tests.py.«math_gcd.py.ast»
import FormalSW

namespace tests.py.math_gcd
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := MathGcdAst.module

theorem pair.result (a b : Int) :
    ReturnsValue program "pair" [.int a, .int b] (.int (Nat.gcd a.natAbs b.natAbs)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.library_call (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)) rfl
  exact congrArg some (Math.gcdCall_pair a b)

theorem pair.«Returns» (a b : Int) : (function program "pair" [.int a, .int b]).Returns :=
  (pair.result a b).returns

theorem empty.«Returns» : (function program "empty" []).Returns := by
  apply ReturnsValue.returns (value := .int 0)
  apply BlockReturns.function rfl rfl
  exact BlockReturns.return_value (Evaluates.library_call .nil rfl rfl)

theorem single.«Returns» (n : Int) : (function program "single" [.int n]).Returns := by
  apply ReturnsValue.returns (value := .int n.natAbs)
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.library_call (.cons (Evaluates.lookup rfl) .nil) rfl
  change some (Except.ok (Constant.int ((Nat.gcd 0 n.natAbs : Nat) : Int))) = _
  simp

theorem booleans.«Returns» (a b : Bool) : (function program "booleans" [.bool a, .bool b]).Returns := by
  apply ReturnsValue.returns (value := .int (if a || b then 1 else 0))
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.library_call (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)) rfl
  cases a <;> cases b <;> rfl

theorem invalid_after_one.throws (value : String) :
    (function program "invalid_after_one" [.string value]).Throws := by
  refine ⟨{ typeName := "TypeError", args := [] }, ?_⟩
  exact Execution.finishes_of_observe (fuel := 10) rfl

end tests.py.math_gcd
