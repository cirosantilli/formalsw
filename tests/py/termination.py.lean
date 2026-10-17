import «.cleanxy».tests.py.«termination.py.ast»
import CleanXY

namespace tests.py.termination
open CleanXY.PyAst

private def foreverLoop : Stmt := .whileDo (.constant (.bool true)) [.expr (.constant .none)] []

private theorem forever_block_diverges (env : ScalarEnv) :
    (scalarBlock [foreverLoop] env).Diverges := by
  refine ⟨fun state => state.todo = [foreverLoop] ∨
    state.todo = [.expr (.constant .none), foreverLoop], Or.inl rfl, ?_⟩
  rintro ⟨todo, env⟩ (h | h)
  · simp only at h
    subst todo
    exact ⟨⟨[.expr (.constant .none), foreverLoop], env⟩, rfl, Or.inr rfl⟩
  · simp only at h
    subst todo
    exact ⟨⟨[foreverLoop], env⟩, rfl, Or.inl rfl⟩

theorem forever.diverges_forever :
    (scalarFunction TerminationAst.module "forever" []).Diverges := by
  simpa [scalarFunction, findFunctionIn, TerminationAst.module, foreverLoop] using
    forever_block_diverges (argumentEnv [] [])

theorem forever.«Not Halts» :
    ¬ (scalarFunction TerminationAst.module "forever" []).Halts :=
  Execution.diverges_not_halts forever.diverges_forever

private def euclidBranch : Stmt :=
  .ifThen (.compare (.name "a") [(.gt, .name "b")])
    [.augAssign (.name "a") .sub (.name "b")]
    [.augAssign (.name "b") .sub (.name "a")]
private def euclidLoop : Stmt :=
  .whileDo (.compare (.name "a") [(.notEq, .name "b")]) [euclidBranch] []

/-- The ranking function is a + b. Every iteration subtracts a positive integer,
so the natural-number rank strictly decreases even though either branch may run. -/
private theorem euclid_finishes (a b : Int) (env : ScalarEnv)
    (positiveA : 0 < a) (positiveB : 0 < b)
    (getA : env "a" = some (.int a)) (getB : env "b" = some (.int b)) :
    ∃ result, Finishes scalarStep ⟨[euclidLoop, .return (.name "a")], env⟩ (.ok result) := by
  by_cases same : a = b
  · refine ⟨.int a, .next (following := ⟨[.return (.name "a")], env⟩) ?_ (.done ?_)⟩
    · simp [scalarStep, euclidLoop, scalarExpr, scalarCompare, evalCmpOp, scalarTruth, getA, getB, same]
    · simp [scalarStep, scalarExpr, getA]
  · by_cases order : b < a
    · obtain ⟨result, finished⟩ := euclid_finishes (a - b) b (env.set "a" (.int (a - b)))
        (by omega) positiveB (by simp [ScalarEnv.set]) (by simp [ScalarEnv.set, getB])
      refine ⟨result, .next (following := ⟨[euclidBranch, euclidLoop, .return (.name "a")], env⟩) ?_
        (.next (following := ⟨[.augAssign (.name "a") .sub (.name "b"),
          euclidLoop, .return (.name "a")], env⟩) ?_ (.next ?_ finished))⟩
      · simp [scalarStep, euclidLoop, scalarExpr, scalarCompare, evalCmpOp, scalarTruth, getA, getB, same]
      · simp [scalarStep, euclidBranch, scalarExpr, scalarCompare, scalarTruth, evalCmpOp, getA, getB, order]
      · simp [scalarStep, scalarExpr, scalarBinary, getA, getB]
    · obtain ⟨result, finished⟩ := euclid_finishes a (b - a) (env.set "b" (.int (b - a)))
        positiveA (by omega) (by simp [ScalarEnv.set, getA]) (by simp [ScalarEnv.set])
      refine ⟨result, .next (following := ⟨[euclidBranch, euclidLoop, .return (.name "a")], env⟩) ?_
        (.next (following := ⟨[.augAssign (.name "b") .sub (.name "a"),
          euclidLoop, .return (.name "a")], env⟩) ?_ (.next ?_ finished))⟩
      · simp [scalarStep, euclidLoop, scalarExpr, scalarCompare, evalCmpOp, scalarTruth, getA, getB, same]
      · simp [scalarStep, euclidBranch, scalarExpr, scalarCompare, scalarTruth, evalCmpOp, getA, getB, order]
      · simp [scalarStep, scalarExpr, scalarBinary, getA, getB]
termination_by (a + b).toNat
decreasing_by all_goals omega

theorem gcd_subtract.«Returns» (a b : Int) :
    (scalarFunction TerminationAst.module "gcd_subtract" [.int a, .int b]).Returns := by
  let env := argumentEnv
    [{ name := "a", annotation := some (.name "int") },
     { name := "b", annotation := some (.name "int") }] [.int a, .int b]
  have getA : env "a" = some (.int a) := by simp [env, argumentEnv]
  have getB : env "b" = some (.int b) := by simp [env, argumentEnv, List.lookup]
  change ∃ result, Finishes scalarStep
    ⟨[.ifThen (.compare (.name "a") [(.ltE, .constant (.int 0))]) [.return (.constant (.int 0))] [],
      .ifThen (.compare (.name "b") [(.ltE, .constant (.int 0))]) [.return (.constant (.int 0))] [],
      euclidLoop, .return (.name "a")], env⟩ (.ok result)
  by_cases positiveA : 0 < a
  · by_cases positiveB : 0 < b
    · obtain ⟨result, finished⟩ := euclid_finishes a b env positiveA positiveB getA getB
      refine ⟨result, .next (following := ⟨[.ifThen (.compare (.name "b") [(.ltE, .constant (.int 0))]) [.return (.constant (.int 0))] [], euclidLoop, .return (.name "a")], env⟩) ?_ (.next ?_ finished)⟩ <;>
        simp [scalarStep, scalarExpr, scalarCompare, evalCmpOp, scalarTruth, getA, getB,
          Int.not_le.mpr positiveA, Int.not_le.mpr positiveB]
    · refine ⟨.int 0, .next (following := ⟨[.ifThen (.compare (.name "b") [(.ltE, .constant (.int 0))]) [.return (.constant (.int 0))] [], euclidLoop, .return (.name "a")], env⟩) ?_ (.next (following := ⟨[.return (.constant (.int 0)), euclidLoop, .return (.name "a")], env⟩) ?_ (.done ?_))⟩ <;>
        simp [scalarStep, scalarExpr, scalarCompare, evalCmpOp, scalarTruth, getA, getB,
          Int.not_le.mpr positiveA, show b ≤ 0 by omega]
  · refine ⟨.int 0, .next (following := ⟨[.return (.constant (.int 0)), .ifThen (.compare (.name "b") [(.ltE, .constant (.int 0))]) [.return (.constant (.int 0))] [], euclidLoop, .return (.name "a")], env⟩) ?_ (.done ?_)⟩ <;>
      simp [scalarStep, scalarExpr, scalarCompare, evalCmpOp, scalarTruth, getA,
        show a ≤ 0 by omega]

theorem implicit_none.«Returns» :
    (scalarFunction TerminationAst.module "implicit_none" []).Returns := by
  refine ⟨.none, Execution.finishes_of_observe (fuel := 2) ?_⟩
  simp [Execution.observe, Execution.observeFrom, scalarFunction, findFunctionIn,
    scalarBlock, executableBody, scalarStep, scalarExpr, TerminationAst.module]

theorem explicit_none.«Returns» :
    (scalarFunction TerminationAst.module "explicit_none" []).Returns := by
  refine ⟨.none, Execution.finishes_of_observe (fuel := 1) ?_⟩
  simp [Execution.observe, Execution.observeFrom, scalarFunction, findFunctionIn,
    scalarBlock, executableBody, scalarStep, scalarExpr, TerminationAst.module]

theorem bare_return.«Returns» :
    (scalarFunction TerminationAst.module "bare_return" []).Returns := by
  refine ⟨.none, Execution.finishes_of_observe (fuel := 1) ?_⟩
  simp [Execution.observe, Execution.observeFrom, scalarFunction, findFunctionIn,
    scalarBlock, executableBody, scalarStep, scalarExpr, TerminationAst.module]

end tests.py.termination
