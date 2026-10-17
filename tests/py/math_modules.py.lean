import «.formalsw».tests.py.«math_modules.py.ast»
import FormalSW

namespace tests.py.math_modules
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := MathModulesAst.module

theorem root.result (n : Nat) :
    ReturnsValue program "root" [.int n] (.int (Math.isqrt n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.qualified_call
  apply Evaluates.library_call (.cons (Evaluates.lookup rfl) .nil) rfl
  change some (Math.isqrtCall [.int n]) = _
  simp [Math.isqrtCall]

theorem root.«Returns» (n : Int) (hp : Calls.Condition program
      (fun key => if key = "n" then some (.int n) else none) MathModulesAst.requires_root_0) :
    (Calls.function program "root" [.int n]).Returns := by
  have hn : n ≥ 0 := by
    simpa [evalCmpOp] using Evaluates.condition_int_compare hp rfl
  simpa [Int.toNat_of_nonneg hn] using (root.result n.toNat).returns

theorem pair.«Returns» (a b : Int) : (function program "pair" [.int a, .int b]).Returns := by
  apply ReturnsValue.returns (value := .int (Nat.gcd a.natAbs b.natAbs))
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.qualified_call
  apply Evaluates.library_call (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)) rfl
  exact congrArg some (Math.gcdCall_pair a b)

-- These are straight-line source executions; the observation bound counts
-- interpreter transitions, while gcd itself is total for arbitrary integers.
theorem heap_pair.«Returns» (a b : Int) :
    (HeapCalls.scalarFunction program "heap_pair" [.int a, .int b]).Returns := by
  refine ⟨.int (Nat.gcd a.natAbs b.natAbs), Execution.finishes_of_observe (fuel := 60) ?_⟩
  change Execution.Observation.done (.ok (Constant.int ((Nat.gcd (Nat.gcd 0 a.natAbs) b.natAbs : Nat) : Int))) = _
  simp

theorem heap_pair.«Supported» (a b : Int) :
    (HeapCalls.scalarFunction program "heap_pair" [.int a, .int b]).Supported :=
  (heap_pair.«Returns» a b).supported

theorem heap_import.«Returns» (a b : Int) :
    (HeapCalls.scalarFunction program "heap_import" [.int a, .int b]).Returns := by
  refine ⟨.int (Nat.gcd a.natAbs b.natAbs), Execution.finishes_of_observe (fuel := 60) ?_⟩
  change Execution.Observation.done (.ok (Constant.int ((Nat.gcd (Nat.gcd 0 a.natAbs) b.natAbs : Nat) : Int))) = _
  simp

theorem heap_import.«Supported» (a b : Int) :
    (HeapCalls.scalarFunction program "heap_import" [.int a, .int b]).Supported :=
  (heap_import.«Returns» a b).supported

-- Linking preserves module imports as well as directly imported functions.
private def prelude : List Stmt := [.functionDef "unrelated" [] none [.return (.constant .none)]]
private theorem extension : Extends { body := prelude ++ program.body } program := by
  apply Extends.prepend
  · intro name member
    simp only [prelude, functionNames, List.mem_cons, List.not_mem_nil, or_false] at member
    subst name
    decide
  · simp [prelude, importNames]

example (n : Nat) : ReturnsValue { body := prelude ++ program.body } "root" [.int n] (.int (Math.isqrt n)) :=
  (root.result n).extend extension

end tests.py.math_modules
