import «.formalsw».tests.py.«math_isqrt.py.ast»
import FormalSW

namespace tests.py.math_isqrt
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := MathIsqrtAst.module

theorem root.result (n : Nat) :
    ReturnsValue program "root" [.int n] (.int (Math.isqrt n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.library_call (.cons (Evaluates.lookup rfl) .nil) rfl
  change some (Math.isqrtCall [.int n]) = _
  simp [Math.isqrtCall]

theorem root.«Returns» (n : Int) (hn : n ≥ 0) :
    (Calls.function program "root" [.int n]).Returns := by
  simpa [Int.toNat_of_nonneg hn] using (root.result n.toNat).returns

theorem root.correct (n : Nat) :
    Math.isqrt n * Math.isqrt n ≤ n ∧ n < (Math.isqrt n + 1) * (Math.isqrt n + 1) :=
  Math.isqrt_spec n

theorem negative.throws (n : Int) (hn : n < 0) :
    (Calls.function program "negative" [.int n]).Throws := by
  refine ⟨{ typeName := "ValueError", args := [] }, ?_⟩
  refine .next rfl (.next rfl (.next rfl (.next rfl (.next rfl (.done ?_)))))
  change outcome (some (Math.isqrtCall [.int n])) [] = _
  simp [outcome, Math.isqrtCall, hn]
  rfl

theorem boolean_root.«Returns» (flag : Bool) :
    (Calls.function program "boolean_root" [.bool flag]).Returns := by
  apply ReturnsValue.returns (value := .int (if flag then 1 else 0))
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.library_call (.cons (Evaluates.lookup rfl) .nil) rfl rfl

theorem bad_type.throws (n : String) :
    (Calls.function program "bad_type" [.string n]).Throws := by
  refine ⟨{ typeName := "TypeError", args := [] }, ?_⟩
  exact Execution.finishes_of_observe (fuel := 8) rfl

example : Math.isqrt (10 ^ 100) = 10 ^ 50 := by native_decide

end tests.py.math_isqrt
