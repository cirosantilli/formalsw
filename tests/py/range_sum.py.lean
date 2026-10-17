import «.formalsw».tests.py.«range_sum.py.ast»
import FormalSW

namespace tests.py.range_sum

/-- `sum` returns an integer for every integer input. -/
theorem sum.returns (n : Int) :
    ∃ value,
      FormalSW.PyAst.evalUnaryIntFunction
          RangeSumAst.module "sum" n =
        some value := by
  by_cases hn : n <= 0
  · refine ⟨0, ?_⟩
    simp [
      FormalSW.PyAst.evalUnaryIntFunction,
      FormalSW.PyAst.Module.findFunctionBody,
      FormalSW.PyAst.findFunctionBodyIn,
      FormalSW.PyAst.evalIntBlock,
      FormalSW.PyAst.evalBoolExpr,
      FormalSW.PyAst.evalIntExpr,
      FormalSW.PyAst.Env.get?,
      FormalSW.PyAst.evalCmpOp,
      RangeSumAst.module,
      hn,
    ]
  · refine ⟨FormalSW.PyAst.sumRange n.toNat, ?_⟩
    simp [
      FormalSW.PyAst.evalUnaryIntFunction,
      FormalSW.PyAst.Module.findFunctionBody,
      FormalSW.PyAst.findFunctionBodyIn,
      FormalSW.PyAst.evalIntBlock,
      FormalSW.PyAst.evalBoolExpr,
      FormalSW.PyAst.evalIntExpr,
      FormalSW.PyAst.Env.get?,
      FormalSW.PyAst.evalCmpOp,
      RangeSumAst.module,
      hn,
    ]

/-- `sum` never throws for an integer input. -/
theorem sum.«Not Throws» :
    Not (FormalSW.Property.Function.AbstractThrows RangeSumAst.module "sum") := by
  rintro ⟨n, exception, hthrow⟩
  by_cases hn : n <= 0
  · simp [
      FormalSW.PyAst.evalUnaryIntFunctionOutcome,
      FormalSW.PyAst.Module.findFunctionBody,
      FormalSW.PyAst.findFunctionBodyIn,
      FormalSW.PyAst.evalIntBlockOutcome,
      FormalSW.PyAst.evalBoolExpr,
      FormalSW.PyAst.evalIntExpr,
      FormalSW.PyAst.Env.get?,
      FormalSW.PyAst.evalCmpOp,
      RangeSumAst.module,
      hn,
    ] at hthrow
  · simp [
      FormalSW.PyAst.evalUnaryIntFunctionOutcome,
      FormalSW.PyAst.Module.findFunctionBody,
      FormalSW.PyAst.findFunctionBodyIn,
      FormalSW.PyAst.evalIntBlockOutcome,
      FormalSW.PyAst.evalBoolExpr,
      FormalSW.PyAst.evalIntExpr,
      FormalSW.PyAst.Env.get?,
      FormalSW.PyAst.evalCmpOp,
      RangeSumAst.module,
      hn,
    ] at hthrow

/-- `sum_naive` returns an integer for every integer input. -/
theorem sum_naive.returns (n : Int) :
    ∃ value,
      FormalSW.PyAst.evalUnaryIntFunction
          RangeSumAst.module "sum_naive" n =
        some value := by
  refine ⟨FormalSW.PyAst.sumRange n.toNat, ?_⟩
  simp [
    FormalSW.PyAst.evalUnaryIntFunction,
    FormalSW.PyAst.Module.findFunctionBody,
    FormalSW.PyAst.findFunctionBodyIn,
    FormalSW.PyAst.evalIntBlock,
    FormalSW.PyAst.evalIntExpr,
    FormalSW.PyAst.evalRangeContribution,
    FormalSW.PyAst.Env.get?,
    RangeSumAst.module,
  ]

/-- `sum_naive` never throws for an integer input. -/
theorem sum_naive.not_throws :
    Not (FormalSW.Property.Function.AbstractThrows RangeSumAst.module "sum_naive") := by
  rintro ⟨n, exception, hthrow⟩
  simp [
    FormalSW.PyAst.evalUnaryIntFunctionOutcome,
    FormalSW.PyAst.Module.findFunctionBody,
    FormalSW.PyAst.findFunctionBodyIn,
    FormalSW.PyAst.evalIntBlockOutcome,
    FormalSW.PyAst.evalIntBlock,
    FormalSW.PyAst.evalIntExpr,
    FormalSW.PyAst.evalRangeContribution,
    FormalSW.PyAst.Env.get?,
    RangeSumAst.module,
  ] at hthrow

/-- Neither range-sum implementation can throw for any integer input. -/
theorem noException (n : Int) :
    (∃ value,
      FormalSW.PyAst.evalUnaryIntFunction
          RangeSumAst.module "sum" n =
        some value) ∧
    (∃ value,
      FormalSW.PyAst.evalUnaryIntFunction
          RangeSumAst.module "sum_naive" n =
        some value) :=
  ⟨sum.returns n, sum_naive.returns n⟩

/-- `sum` and `sum_naive` give the same result for every integer input. -/
private theorem sum.abstract_equiv :
    FormalSW.Property.Function.AbstractEquiv
      RangeSumAst.module "sum" "sum_naive" := by
  intro n
  by_cases hn : n <= 0
  · refine ⟨.ok 0, ?_⟩
    constructor <;> simp [
      FormalSW.PyAst.evalUnaryIntFunctionOutcome,
      FormalSW.PyAst.Module.findFunctionBody,
      FormalSW.PyAst.findFunctionBodyIn,
      FormalSW.PyAst.evalIntBlockOutcome,
      FormalSW.PyAst.evalIntBlock,
      FormalSW.PyAst.evalBoolExpr,
      FormalSW.PyAst.evalIntExpr,
      FormalSW.PyAst.evalRangeContribution,
      FormalSW.PyAst.sumRange,
      FormalSW.PyAst.Env.get?,
      FormalSW.PyAst.evalCmpOp,
      RangeSumAst.module,
      hn,
      Int.toNat_of_nonpos hn,
    ]
  · refine ⟨.ok (FormalSW.PyAst.sumRange n.toNat), ?_⟩
    constructor <;> simp [
      FormalSW.PyAst.evalUnaryIntFunctionOutcome,
      FormalSW.PyAst.Module.findFunctionBody,
      FormalSW.PyAst.findFunctionBodyIn,
      FormalSW.PyAst.evalIntBlockOutcome,
      FormalSW.PyAst.evalIntBlock,
      FormalSW.PyAst.evalBoolExpr,
      FormalSW.PyAst.evalIntExpr,
      FormalSW.PyAst.evalRangeContribution,
      FormalSW.PyAst.Env.get?,
      FormalSW.PyAst.evalCmpOp,
      RangeSumAst.module,
      hn,
    ]

/-- The closed-form implementation has constant worst-case cost. -/
theorem sum.«BigO(1)» :
    FormalSW.Property.Function.BigO RangeSumAst.module "sum"
      (.intToNat "n") (fun _ => 1) := by
  apply FormalSW.Property.Function.bigO_of_growth_bound
    (inputSize := .intToNat "n") (growth := .constant)
  · rfl
  · rfl
  · exact FormalSW.PyAst.Growth.constant_isBigO

/-- The loop implementation has linear worst-case cost. -/
theorem sum_naive.«BigO(n)» :
    FormalSW.Property.Function.BigO RangeSumAst.module "sum_naive"
      (.intToNat "n") (fun n => n) := by
  apply FormalSW.Property.Function.bigO_of_growth_bound
    (inputSize := .intToNat "n") (growth := .linear)
  · rfl
  · rfl
  · exact FormalSW.PyAst.Growth.linear_isBigO

open FormalSW.PyAst

private def sumLoop (index stop : Int) : Stmt :=
  .rangeLoop "i" index stop [.augAssign (.name "total") .add (.name "i")] []

private theorem sum_loop_finishes (index stop total : Int) (env : ScalarEnv)
    (getTotal : env "total" = some (.int total)) :
    ∃ result, Finishes scalarStep ⟨[sumLoop index stop, .return (.name "total")], env⟩ (.ok result) := by
  by_cases active : index < stop
  · let updated := (env.set "i" (.int index)).set "total" (.int (total + index))
    obtain ⟨result, finished⟩ := sum_loop_finishes (index + 1) stop (total + index) updated
      (by simp [updated, ScalarEnv.set])
    refine ⟨result, .next
      (following := ⟨[.augAssign (.name "total") .add (.name "i"),
        sumLoop (index + 1) stop, .return (.name "total")], env.set "i" (.int index)⟩)
      ?_ (.next ?_ finished)⟩
    · simp [scalarStep, sumLoop, active]
    · simp [scalarStep, scalarExpr, scalarBinary, ScalarEnv.set, getTotal, updated]
  · refine ⟨.int total, .next (following := ⟨[.return (.name "total")], env⟩) ?_ (.done ?_)⟩
    · simp [scalarStep, sumLoop, active]
    · simp [scalarStep, scalarExpr, getTotal]
termination_by (stop - index).toNat
decreasing_by omega

/-- The finite range loop terminates for every integer n, including n <= 0. -/
theorem sum_naive.«Returns» (n : Int) :
    (scalarFunction RangeSumAst.module "sum_naive" [.int n]).Returns := by
  let env := argumentEnv [{ name := "n", annotation := some (.name "int") }] [.int n]
  let updated := env.set "total" (.int 0)
  obtain ⟨result, finished⟩ := sum_loop_finishes 0 n 0 updated (by simp [updated, ScalarEnv.set])
  change ∃ result, Finishes scalarStep
    ⟨[.assign [.name "total"] (.constant (.int 0)),
      .forIn (.name "i") (.call (.name "range") [.name "n"])
        [.augAssign (.name "total") .add (.name "i")] [],
      .return (.name "total")], env⟩ (.ok result)
  refine ⟨result, .next (following := ⟨[
    .forIn (.name "i") (.call (.name "range") [.name "n"])
      [.augAssign (.name "total") .add (.name "i")] [],
    .return (.name "total")], updated⟩) ?_ (.next ?_ finished)⟩
  · rfl
  · simp [scalarStep, scalarExpr, updated, env, ScalarEnv.set, argumentEnv, sumLoop]

private theorem sum_loop_result (index stop total : Int) (env : ScalarEnv)
    (getTotal : env "total" = some (.int total))
    (nonnegative : 0 ≤ index) (bound : index ≤ stop)
    (invariant : 2 * total = index * (index - 1)) :
    Finishes scalarStep ⟨[sumLoop index stop, .return (.name "total")], env⟩
      (.ok (.int (stop * (stop - 1) / 2))) := by
  by_cases active : index < stop
  · let updated := (env.set "i" (.int index)).set "total" (.int (total + index))
    have next_invariant : 2 * (total + index) = (index + 1) * (index + 1 - 1) := by
      simp only [Int.add_sub_cancel, Int.mul_add, Int.add_mul, Int.one_mul]
      simp only [Int.mul_sub, Int.mul_one] at invariant
      omega
    have rest := sum_loop_result (index + 1) stop (total + index) updated
      (by simp [updated, ScalarEnv.set]) (by omega) (by omega) next_invariant
    refine .next
      (following := ⟨[.augAssign (.name "total") .add (.name "i"),
        sumLoop (index + 1) stop, .return (.name "total")], env.set "i" (.int index)⟩)
      ?_ (.next ?_ rest)
    · simp [scalarStep, sumLoop, active]
    · simp [scalarStep, scalarExpr, scalarBinary, ScalarEnv.set, getTotal, updated]
  · have same : index = stop := by omega
    have result : total = stop * (stop - 1) / 2 := by rw [same] at invariant; omega
    refine .next (following := ⟨[.return (.name "total")], env⟩) ?_ (.done ?_)
    · simp [scalarStep, sumLoop, active]
    · simp [scalarStep, scalarExpr, getTotal, result]
termination_by (stop - index).toNat
decreasing_by omega

private theorem sum_naive.result (n : Int) :
    Finishes (scalarFunction RangeSumAst.module "sum_naive" [.int n]).step
      (scalarFunction RangeSumAst.module "sum_naive" [.int n]).initial
      (.ok (.int (if n ≤ 0 then 0 else n * (n - 1) / 2))) := by
  let env := argumentEnv [{ name := "n", annotation := some (.name "int") }] [.int n]
  let updated := env.set "total" (.int 0)
  change Finishes scalarStep
    ⟨[.assign [.name "total"] (.constant (.int 0)),
      .forIn (.name "i") (.call (.name "range") [.name "n"])
        [.augAssign (.name "total") .add (.name "i")] [],
      .return (.name "total")], env⟩ _
  refine .next (following := ⟨[
    .forIn (.name "i") (.call (.name "range") [.name "n"])
      [.augAssign (.name "total") .add (.name "i")] [],
    .return (.name "total")], updated⟩) rfl
    (.next (following := ⟨[sumLoop 0 n, .return (.name "total")], updated⟩) ?_ ?_)
  · simp [scalarStep, scalarExpr, updated, env, ScalarEnv.set, argumentEnv, sumLoop]
  · by_cases nonpositive : n ≤ 0
    · simp only [nonpositive, ↓reduceIte]
      refine .next (following := ⟨[.return (.name "total")], updated⟩) ?_ (.done rfl)
      simp [scalarStep, sumLoop, nonpositive]
    · simp only [nonpositive, ↓reduceIte]
      exact sum_loop_result 0 n 0 updated (by simp [updated, ScalarEnv.set])
        (by omega) (by omega) (by simp)

private theorem sum.result (n : Int) :
    Finishes (scalarFunction RangeSumAst.module "sum" [.int n]).step
      (scalarFunction RangeSumAst.module "sum" [.int n]).initial
      (.ok (.int (if n ≤ 0 then 0 else n * (n - 1) / 2))) := by
  apply Execution.finishes_of_observe (fuel := 2)
  by_cases nonpositive : n ≤ 0 <;>
    simp [Execution.observe, Execution.observeFrom, scalarFunction, findFunctionIn,
      scalarBlock, executableBody, scalarStep, scalarExpr, scalarCompare, scalarBinary,
      scalarTruth, argumentEnv, evalCmpOp, RangeSumAst.module, nonpositive]

/-- The closed form finishes with an integer of its annotated return type. -/
theorem sum.«ReturnType» :
    FormalSW.Property.Function.ReturnType RangeSumAst.module "sum" := by
  intro n
  exact Or.inl ⟨_, sum.result n⟩

/-- Actual execution outcomes agree, so termination contracts transfer too. -/
theorem sum.«Equiv(sum_naive)» :
    FormalSW.Property.Function.Equiv RangeSumAst.module "sum" "sum_naive" := by
  intro n outcome
  constructor
  · intro h
    have same := h.unique (sum.result n)
    rw [same]
    exact sum_naive.result n
  · intro h
    have same := h.unique (sum_naive.result n)
    rw [same]
    exact sum.result n

/-- No duplicate Returns marker is needed on the equivalent implementation. -/
example (n : Int) : (scalarFunction RangeSumAst.module "sum" [.int n]).Returns :=
  (sum.«Equiv(sum_naive)» n).returns_iff.mpr (sum_naive.«Returns» n)

end tests.py.range_sum
