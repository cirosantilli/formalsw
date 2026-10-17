import «.formalsw».tests.py.«loop_control.py.ast»
import FormalSW

namespace tests.py.loop_control
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := LoopControlAst.module

private def countdownBody : List Stmt :=
  [.ifThen (.compare (.name "n") [(.eq, .constant (.int 0))]) [.breakLoop] [],
   .augAssign (.name "n") .sub (.constant (.int 1)), .continueLoop,
   .augAssign (.name "n") .floorDiv (.constant (.int 0))]

private def countdownLoop : List Stmt :=
  [.whileDo (.constant (.bool true)) countdownBody [.return (.constant (.int 99))],
   .return (.name "n")]

private theorem countdown_loop (n : Nat) (env : ScalarEnv) (hn : env "n" = some (.int n)) :
    BlockReturns program env countdownLoop (.int 0) := by
  induction n generalizing env with
  | zero =>
      apply BlockReturns.while_loop Evaluates.constant
      apply BlockReturns.branch (value := .bool true)
      · exact Evaluates.compare (Evaluates.lookup hn) Evaluates.constant rfl
      · apply BlockReturns.break_loop rfl
        exact BlockReturns.return_value (Evaluates.lookup hn)
  | succ n ih =>
      apply BlockReturns.while_loop Evaluates.constant
      apply BlockReturns.branch (value := .bool false)
      · exact Evaluates.compare (Evaluates.lookup hn) Evaluates.constant
          (by simp [scalarCompare, evalCmpOp]; omega)
      · apply BlockReturns.augAssign (value := .int n)
        · exact Evaluates.binary (Evaluates.lookup hn) Evaluates.constant (by simp [scalarBinary])
        · apply BlockReturns.continue_loop rfl
          exact ih _ (by simp [ScalarEnv.set])

theorem countdown.«Returns» (n : Int) (hp : Calls.Condition program
    (fun key => if key = "n" then some (.int n) else none) LoopControlAst.requires_countdown_0) :
    (Calls.function program "countdown" [.int n]).Returns := by
  have nonnegative : n ≥ 0 := by simpa [evalCmpOp] using Evaluates.condition_int_compare hp rfl
  have result : ReturnsValue program "countdown" [.int n.toNat] (.int 0) := by
    apply BlockReturns.function rfl rfl
    exact countdown_loop n.toNat _ rfl
  simpa [Int.toNat_of_nonneg nonnegative] using result.returns

theorem first.«Returns» (n : Int) : (Calls.function program "first" [.int n]).Returns := by
  apply ReturnsValue.returns (value := .int n)
  apply BlockReturns.function rfl rfl
  apply BlockReturns.for_range (values := [.int n, .int (n + 3)])
  · exact .cons (Evaluates.lookup rfl) (.cons
      (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary])) .nil)
  · rfl
  · apply BlockReturns.range_step (by simp [rangeContinues]; omega)
    apply BlockReturns.break_loop rfl
    exact BlockReturns.return_value (Evaluates.lookup rfl)

private def skipBody : List Stmt :=
  [.assign [.name "k"] (.constant (.int 999)), .continueLoop,
   .return (.unaryOp .uSub (.constant (.int 3)))]

private theorem skip_loop (k : Nat) (n : Int) (env : ScalarEnv) (hn : env "n" = some (.int n)) :
    BlockReturns program env
      [.rangeStepLoop "k" k 0 (-1) skipBody [.return (.name "n")],
       .return (.unaryOp .uSub (.constant (.int 1)))] (.int n) := by
  induction k generalizing env with
  | zero =>
      apply BlockReturns.range_done (by simp [rangeContinues])
      exact BlockReturns.return_value (Evaluates.lookup hn)
  | succ k ih =>
      apply BlockReturns.range_step (by simp [rangeContinues])
      apply BlockReturns.assign Evaluates.constant
      apply BlockReturns.continue_loop rfl
      simpa [Int.add_assoc] using ih ((env.set "k" (.int ↑(k + 1))).set "k" (.int 999))
        (by simp [ScalarEnv.set, hn])

theorem skip.«Returns» (n : Int) (hp : Calls.Condition program
    (fun key => if key = "n" then some (.int n) else none) LoopControlAst.requires_skip_0) :
    (Calls.function program "skip" [.int n]).Returns := by
  have nonnegative : n ≥ 0 := by simpa [evalCmpOp] using Evaluates.condition_int_compare hp rfl
  have result : ReturnsValue program "skip" [.int n.toNat] (.int n.toNat) := by
    apply BlockReturns.function rfl rfl
    apply BlockReturns.for_range (values := [.int n.toNat, .int 0, .int (-1)])
    · exact .cons (Evaluates.lookup rfl) (.cons Evaluates.constant
        (.cons (Evaluates.unary Evaluates.constant rfl) .nil))
    · rfl
    · exact skip_loop n.toNat n.toNat _ rfl
  simpa [Int.toNat_of_nonneg nonnegative] using result.returns

theorem nested.«Returns» (n : Int) : (Calls.function program "nested" [.int n]).Returns := by
  refine ⟨.int 1033, ?_⟩
  exact Execution.finishes_of_observe (fuel := 400) rfl

theorem inner_else_break.«Returns» (n : Int) :
    (Calls.function program "inner_else_break" [.int n]).Returns := by
  refine ⟨.int 0, ?_⟩
  exact Execution.finishes_of_observe (fuel := 100) rfl

theorem inner_else_continue.«Returns» (n : Int) :
    (Calls.function program "inner_else_continue" [.int n]).Returns := by
  refine ⟨.int 1003, ?_⟩
  exact Execution.finishes_of_observe (fuel := 300) rfl

theorem calling.«Returns» (n : Int) : (Calls.function program "calling" [.int n]).Returns := by
  refine ⟨.int (0 + (n + 1) + (n + 1) + (n + 1)), ?_⟩
  exact Execution.finishes_of_observe (fuel := 400) rfl

theorem return_in_loop.«Returns» (n : Int) :
    (Calls.function program "return_in_loop" [.int n]).Returns := by
  refine ⟨.int n, ?_⟩
  exact Execution.finishes_of_observe (fuel := 100) rfl

theorem exception_in_loop.«Throws» : ∃ n : Int, (Calls.function program "exception_in_loop" [.int n]).Throws := by
  refine ⟨0, { typeName := "ZeroDivisionError", args := [] }, ?_⟩
  exact Execution.finishes_of_observe (fuel := 100) rfl

theorem fallthrough.«Returns» (n : Int) : (Calls.function program "fallthrough" [.int n]).Returns := by
  refine ⟨.int 1, ?_⟩
  exact Execution.finishes_of_observe (fuel := 300) rfl

end tests.py.loop_control
