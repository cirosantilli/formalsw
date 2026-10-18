import «.formalsw».tests.py.«requires.py.ast»
import FormalSW

namespace tests.py.requires
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := RequiresAst.module
private def env (n : Int) : ScalarEnv := fun name => if name = "n" then some (.int n) else none
private abbrev allowed (n : Int) := Condition program (env n) RequiresAst.requires_guarded_0

private theorem at_least_result (n : Int) :
    ReturnsValue program "at_least" [.int n, .int 0] (.bool (decide (n ≥ 0))) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.branch (value := .bool true)
  · exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant rfl
  · exact BlockReturns.return_value (Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant rfl)

private theorem allowed_iff (n : Int) : allowed n ↔ n ≥ 0 := by
  have run : Evaluates program (env n) RequiresAst.requires_guarded_0 (.bool (decide (n ≥ 0))) :=
    Evaluates.call (.cons (Evaluates.lookup rfl) (.cons Evaluates.constant .nil)) (at_least_result n)
  simpa using run.condition_iff

private theorem guarded_result (n : Int) (hp : allowed n) :
    Finishes (scalarFunction program "guarded" [.int n]).step
      (scalarFunction program "guarded" [.int n]).initial (.ok (.int n)) := by
  have hn := (allowed_iff n).mp hp
  apply Execution.finishes_of_observe (fuel := 2)
  simp [Execution.observe, Execution.observeFrom, scalarFunction, scalarBlock,
    findFunctionIn, executableBody, scalarStep, scalarExpr, scalarCompare,
    evalCmpOp, scalarTruth, argumentEnv, RequiresAst.module, Int.not_lt_of_ge hn]

theorem guarded.«Returns» (n : Int) (hp : allowed n) :
    (scalarFunction program "guarded" [.int n]).Returns := ⟨_, guarded_result n hp⟩

theorem guarded.«Halts» (n : Int) (hp : allowed n) :
    (scalarFunction program "guarded" [.int n]).Halts := ⟨_, guarded_result n hp⟩

theorem guarded.«Not Throws» : ¬ ∃ n : Int, allowed n ∧
    (scalarFunction program "guarded" [.int n]).Throws := by
  rintro ⟨n, hp, exception, thrown⟩
  have impossible := (guarded_result n hp).unique thrown
  cases impossible

theorem guarded.«ReturnType» (n : Int) (hp : allowed n) :
    (scalarFunction program "guarded" [.int n]).ReturnType "int" :=
  .inr ⟨.int n, guarded_result n hp, rfl⟩

theorem guarded.«Equiv(identity)» (n : Int) (hp : allowed n) :
    (scalarFunction program "guarded" [.int n]).Equiv
      (scalarFunction program "identity" [.int n]) := by
  have left := guarded_result n hp
  have right : Finishes (scalarFunction program "identity" [.int n]).step
      (scalarFunction program "identity" [.int n]).initial (.ok (.int n)) := .done rfl
  intro outcome
  constructor
  · intro h
    rw [h.unique left]
    exact right
  · intro h
    rw [h.unique right]
    exact left

theorem guarded.«EquivReturn(identity)» (n : Int) (hp : allowed n) :
    (scalarFunction program "guarded" [.int n]).EquivReturn
      (scalarFunction program "identity" [.int n]) := by
  intro a b ha hb
  exact Except.ok.inj (((guarded.«Equiv(identity)» n hp) _ |>.mp ha).unique hb)

theorem guarded.«BigO(1)» (n : Int) (_hp : allowed n) :
    FormalSW.Property.Function.BigO program "guarded" (.intToNat "n") (fun _ => 1) := by
  apply FormalSW.Property.Function.bigO_of_growth_bound
    (inputSize := .intToNat "n") (growth := .constant)
  · rfl
  · rfl
  · exact Growth.constant_isBigO

theorem guarded.correct (n : Int) (hp : allowed n) :
    (scalarFunction program "guarded" [.int n]).Returns := guarded.«Returns» n hp

theorem guarded.quantified (n : Int) (hp : allowed n) :
    (scalarFunction program "guarded" [.int n]).Returns := guarded.«Returns» n hp

theorem guarded.witnessed : ∃ n : Int, allowed n ∧
    (scalarFunction program "guarded" [.int n]).Returns := by
  have hp : allowed 0 := (allowed_iff 0).mpr (by decide)
  exact ⟨0, hp, guarded.«Returns» 0 hp⟩

theorem negative.«Throws» : ∃ n : Int,
    Condition program (env n) RequiresAst.requires_negative_0 ∧
    (scalarFunction program "negative" [.int n]).Throws := by
  refine ⟨-1, ?_, ⟨{ typeName := "ZeroDivisionError", args := [] }, .done rfl⟩⟩
  exact Execution.finishes_of_observe (fuel := 10) rfl

theorem truthy.impossible (hp : Condition program (fun _ => none) RequiresAst.requires_truthy_0) : False := by
  have run : Evaluates program (fun _ => none) RequiresAst.requires_truthy_0 (.int 1) := Evaluates.constant
  cases run.condition_iff.mp hp

theorem exceptional.impossible
    (hp : Condition program (fun _ => none) RequiresAst.requires_exceptional_0) : False := by
  have thrown : Finishes (evaluate program (fun _ => none) RequiresAst.requires_exceptional_0).step
      (evaluate program (fun _ => none) RequiresAst.requires_exceptional_0).initial
      (.error { typeName := "ZeroDivisionError", args := [] }) :=
    Execution.finishes_of_observe (fuel := 20) rfl
  cases hp.unique thrown

private theorem chain_true : Condition program (fun _ => none) RequiresAst.requires_chain_0 :=
  Execution.finishes_of_observe (fuel := 100) rfl

theorem chain.«Returns» (n : Int)
    (_hp : Condition program (fun _ => none) RequiresAst.requires_chain_0) :
    (scalarFunction program "chain" [.int n]).Returns := ⟨.int n, .done rfl⟩

theorem short_chain.impossible
    (hp : Condition program (fun _ => none) RequiresAst.requires_short_chain_0) : False := by
  have result : Finishes (evaluate program (fun _ => none) RequiresAst.requires_short_chain_0).step
      (evaluate program (fun _ => none) RequiresAst.requires_short_chain_0).initial (.ok (.bool false)) :=
    Execution.finishes_of_observe (fuel := 30) rfl
  cases hp.unique result

private theorem arithmetic_true : Condition program (fun _ => none) RequiresAst.requires_arithmetic_0 :=
  Execution.finishes_of_observe (fuel := 300) rfl

theorem arithmetic.«Returns» (n : Int)
    (_hp : Condition program (fun _ => none) RequiresAst.requires_arithmetic_0) :
    (scalarFunction program "arithmetic" [.int n]).Returns := ⟨.int n, .done rfl⟩

end tests.py.requires
