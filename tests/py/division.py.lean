import «.formalsw».tests.py.«division.py.ast»
import FormalSW

namespace tests.py.division
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := DivisionAst.module

private def divValue (n d : Int) := if 0 < d then n / d else (-n) / (-d)
private def modValue (n d : Int) := if 0 < d then n % d else n - d * ((-n) / (-d))

private theorem division (n d : Int) (hd : d ≠ 0) :
    scalarBinary .floorDiv (.int n) (.int d) = some (.ok (.int (divValue n d))) := by
  by_cases pos : 0 < d <;> simp [scalarBinary, hd, divValue, pos]

private theorem modulo (n d : Int) (hd : d ≠ 0) :
    scalarBinary .mod (.int n) (.int d) = some (.ok (.int (modValue n d))) := by
  by_cases pos : 0 < d <;> simp [scalarBinary, hd, modValue, pos]

theorem quotient.result (n d : Int) (hd : d ≠ 0) :
    ReturnsValue program "quotient" [.int n, .int d] (.int (divValue n d)) := by
  apply BlockReturns.function rfl rfl
  exact BlockReturns.return_value (Evaluates.binary (Evaluates.lookup rfl)
    (Evaluates.lookup rfl) (division n d hd))

theorem quotient.«Returns» (n d : Int) (hp : Calls.Condition program
    (fun key => if key = "d" then some (.int d) else none) DivisionAst.requires_quotient_0) :
    (Calls.function program "quotient" [.int n, .int d]).Returns := by
  have hd : d ≠ 0 := by simpa [evalCmpOp] using Evaluates.condition_int_compare hp rfl
  exact (quotient.result n d hd).returns

theorem remainder.«Returns» (n d : Int) (hp : Calls.Condition program
    (fun key => if key = "d" then some (.int d) else none) DivisionAst.requires_remainder_0) :
    (Calls.function program "remainder" [.int n, .int d]).Returns := by
  have hd : d ≠ 0 := by simpa [evalCmpOp] using Evaluates.condition_int_compare hp rfl
  have result : ReturnsValue program "remainder" [.int n, .int d] (.int (modValue n d)) := by
    apply BlockReturns.function rfl rfl
    exact BlockReturns.return_value (Evaluates.binary (Evaluates.lookup rfl)
      (Evaluates.lookup rfl) (modulo n d hd))
  exact result.returns

theorem negative.«Returns» (n : Int) :
    (Calls.function program "negative" [.int n]).Returns := by
  have result : ReturnsValue program "negative" [.int n] (.int (modValue n (-2))) := by
    apply BlockReturns.function rfl rfl
    exact BlockReturns.return_value (Evaluates.binary (Evaluates.lookup rfl)
      (Evaluates.unary Evaluates.constant rfl) (modulo n (-2) (by decide)))
  exact result.returns

theorem augmented.«Returns» (n d : Int) (hp : Calls.Condition program
    (fun key => if key = "d" then some (.int d) else none) DivisionAst.requires_augmented_0) :
    (Calls.function program "augmented" [.int n, .int d]).Returns := by
  have hd : d ≠ 0 := by simpa [evalCmpOp] using Evaluates.condition_int_compare hp rfl
  have result : ReturnsValue program "augmented" [.int n, .int d] (.int (divValue n d)) := by
    apply BlockReturns.function rfl rfl
    apply BlockReturns.augAssign (Evaluates.binary (Evaluates.lookup rfl)
      (Evaluates.lookup rfl) (division n d hd))
    exact BlockReturns.return_value (Evaluates.lookup rfl)
  exact result.returns

example : (Calls.function program "quotient" [.int 7, .int 0]).Throws := by
  refine ⟨{ typeName := "ZeroDivisionError", args := [] }, ?_⟩
  exact Execution.finishes_of_observe (fuel := 12) rfl

end tests.py.division
