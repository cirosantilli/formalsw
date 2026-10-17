import «.formalsw».tests.py.«requires_imported.py.ast»
import tests.py.«link_reference.py»
import FormalSW

namespace tests.py.requires_imported
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := RequiresImportedAst.module
private def env (n : Int) : ScalarEnv := fun name => if name = "n" then some (.int n) else none
private abbrev allowed (n : Int) := Condition program (env n) RequiresImportedAst.requires_checked_0

private theorem extends_reference : Extends program LinkReferenceAst.module := by
  change Extends { body := program.body.take 2 ++ LinkReferenceAst.module.body } LinkReferenceAst.module
  apply Extends.prepend
  · intro name member
    change name ∈ ["checked", "_formalsw_requires_target"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

theorem allowed_iff (n : Int) : allowed n ↔ n ≥ 0 := by
  have reference := (link_reference.double.result n).extend extends_reference
  have alias_result : ReturnsValue program "_formalsw_requires_target" [.int n] (.int (n + n)) := by
    apply BlockReturns.function rfl rfl
    exact BlockReturns.return_value (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) reference)
  have run : Evaluates program (env n) RequiresImportedAst.requires_checked_0
      (.bool (decide (n + n ≥ 0))) :=
    Evaluates.compare (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) alias_result)
      Evaluates.constant rfl
  have result := run.condition_iff
  simp only [Constant.bool.injEq, decide_eq_true_eq] at result
  change allowed n ↔ n + n ≥ 0 at result
  rw [result]
  omega

private theorem checked.result (n : Int) (hp : allowed n) :
    Finishes (scalarFunction program "checked" [.int n]).step
      (scalarFunction program "checked" [.int n]).initial (.ok (.int n)) := by
  have hn := (allowed_iff n).mp hp
  apply Execution.finishes_of_observe (fuel := 2)
  simp [Execution.observe, Execution.observeFrom, scalarFunction, scalarBlock,
    findFunctionIn, executableBody, scalarStep, scalarExpr, scalarCompare,
    evalCmpOp, scalarTruth, argumentEnv, RequiresImportedAst.module, Int.not_lt_of_ge hn]

theorem checked.«Returns» (n : Int) (hp : allowed n) :
    (scalarFunction program "checked" [.int n]).Returns := ⟨_, checked.result n hp⟩

theorem checked.«ReturnType» (n : Int) (hp : allowed n) :
    (scalarFunction program "checked" [.int n]).ReturnType "int" :=
  .inr ⟨_, checked.result n hp, rfl⟩

end tests.py.requires_imported
