import «.formalsw».tests.py.«powers.py.ast»
import FormalSW

namespace tests.py.powers
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := PowersAst.module

theorem power.result (base exponent : Int) (nonnegative : 0 ≤ exponent) :
    ReturnsValue program "power" [.int base, .int exponent] (.int (base ^ exponent.toNat)) := by
  apply BlockReturns.function rfl rfl
  exact BlockReturns.return_value (Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl)
    (by simp [scalarBinary, Int.not_lt.mpr nonnegative]))

theorem power.«Returns» (base exponent : Int) (hp : Calls.Condition program
    (fun key => if key = "exponent" then some (.int exponent) else none) PowersAst.requires_power_0) :
    (Calls.function program "power" [.int base, .int exponent]).Returns := by
  have hn : 0 ≤ exponent := by simpa [evalCmpOp] using Evaluates.condition_int_compare hp rfl
  exact (power.result base exponent hn).returns

theorem power.«Supported» (base exponent : Int) (hp : Calls.Condition program
    (fun key => if key = "exponent" then some (.int exponent) else none) PowersAst.requires_power_0) :
    (Calls.function program "power" [.int base, .int exponent]).Supported :=
  (power.«Returns» base exponent hp).supported

theorem digit_lower.«Returns» (n : Int) (hp : Calls.Condition program
    (fun key => if key = "n" then some (.int n) else none) PowersAst.requires_digit_lower_0) :
    (Calls.function program "digit_lower" [.int n]).Returns := by
  have hn : 0 ≤ n := by simpa [evalCmpOp] using Evaluates.condition_int_compare hp rfl
  apply ReturnsValue.returns (value := .int (if n = 0 then 0 else 10 ^ (n - 1).toNat))
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.conditional (c := .bool (decide (n = 0)))
  · exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant rfl
  · by_cases zero : n = 0
    · simp only [zero, decide_true, scalarTruth, ↓reduceIte]
      exact Evaluates.constant
    · simp only [zero, decide_false, scalarTruth, ↓reduceIte]
      apply Evaluates.binary Evaluates.constant (bv := .int (n - 1))
      · exact Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl
      · simp [scalarBinary, show ¬n - 1 < 0 by omega]

theorem digit_lower.«Supported» (n : Int) (hp : Calls.Condition program
    (fun key => if key = "n" then some (.int n) else none) PowersAst.requires_digit_lower_0) :
    (Calls.function program "digit_lower" [.int n]).Supported :=
  (digit_lower.«Returns» n hp).supported

theorem square.«Returns» (n : Int) : (Calls.function program "square" [.int n]).Returns := by
  apply ReturnsValue.returns (value := .int (n ^ 2))
  apply BlockReturns.function rfl rfl
  apply BlockReturns.augAssign (value := .int (n ^ 2))
  · exact Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary, Int.pow_succ])
  · exact BlockReturns.return_value (Evaluates.lookup rfl)

theorem square.«Supported» (n : Int) : (Calls.function program "square" [.int n]).Supported :=
  (square.«Returns» n).supported

theorem boolean_exponents.«Returns» (n : Int) :
    (Calls.function program "boolean_exponents" [.int n]).Returns := by
  apply ReturnsValue.returns (value := .int (1 + n))
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary (av := .int 1) (bv := .int n)
  · exact Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary])
  · exact Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary, Int.pow_succ])
  · rfl

theorem boolean_exponents.«Supported» (n : Int) :
    (Calls.function program "boolean_exponents" [.int n]).Supported :=
  (boolean_exponents.«Returns» n).supported

private theorem ordered.run (n : Int) : Finishes (Calls.function program "ordered" [.int n]).step
    (Calls.function program "ordered" [.int n]).initial
      (.error { typeName := "ZeroDivisionError", args := [] }) :=
  Execution.finishes_of_observe (fuel := 30) rfl

theorem ordered.«Throws» : ∃ n : Int, (Calls.function program "ordered" [.int n]).Throws :=
  ⟨0, _, ordered.run 0⟩

theorem ordered.«Supported» (n : Int) : (Calls.function program "ordered" [.int n]).Supported :=
  Execution.supported_of_finishes (ordered.run n)

private theorem squared.result (n : Int) : ReturnsValue program "squared" [.int n] (.int (n * n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.call (.cons (Evaluates.lookup rfl) (.cons Evaluates.constant .nil))
  simpa [Int.pow_succ] using power.result n 2 (by decide)

private theorem reference.run (n : Int) : Finishes (scalarFunction program "square_reference" [.int n]).step
    (scalarFunction program "square_reference" [.int n]).initial (.ok (.int (n * n))) :=
  Execution.finishes_of_observe (fuel := 5) rfl

theorem squared.«Equiv(square_reference)» (n : Int) :
    (Calls.function program "squared" [.int n]).Equiv (scalarFunction program "square_reference" [.int n]) := by
  intro result
  constructor
  · intro run
    rw [run.unique (squared.result n).finishes]
    exact reference.run n
  · intro run
    rw [run.unique (reference.run n)]
    exact (squared.result n).finishes

theorem squared.«Supported» :
    (∀ n : Int, (Calls.function program "squared" [.int n]).Supported) ∧
    (∀ n : Int, (scalarFunction program "square_reference" [.int n]).Supported) :=
  ⟨fun n => (squared.result n).returns.supported, fun n => Execution.supported_of_finishes (reference.run n)⟩

theorem guarded.«Returns» (n : Int)
    (_ : Calls.Condition program (fun key => if key = "n" then some (.int n) else none) PowersAst.requires_guarded_0)
    (_ : Calls.Condition program (fun key => if key = "n" then some (.int n) else none) PowersAst.requires_guarded_1) :
    (scalarFunction program "guarded" [.int n]).Returns :=
  ⟨.int n, Execution.finishes_of_observe (fuel := 5) rfl⟩

theorem requires_guarded_1_supported (n : Int) (hp : Calls.Condition program
    (fun key => if key = "n" then some (.int n) else none) PowersAst.requires_guarded_0) :
    (Calls.evaluate program (fun key => if key = "n" then some (.int n) else none)
      PowersAst.requires_guarded_1).Supported := by
  have hn : 0 ≤ n := by simpa [evalCmpOp] using Evaluates.condition_int_compare hp rfl
  have evaluated : Evaluates program (fun key => if key = "n" then some (.int n) else none)
      PowersAst.requires_guarded_1 (.bool (decide ((10 : Int) ^ n.toNat > 0))) := by
    apply Evaluates.compare (av := .int (10 ^ n.toNat)) (bv := .int 0)
    · exact Evaluates.binary Evaluates.constant (Evaluates.lookup rfl)
        (by simp [scalarBinary, Int.not_lt.mpr hn])
    · exact Evaluates.constant
    · rfl
  exact Execution.supported_of_finishes evaluated.finishes

end tests.py.powers
