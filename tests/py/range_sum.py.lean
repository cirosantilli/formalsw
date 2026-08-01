import «.cleanxy».tests.py.«range_sum.py.ast»
import CleanXY

namespace tests.py.range_sum

/-- `sum` returns an integer for every integer input. -/
theorem sum.returns (n : Int) :
    ∃ value,
      CleanXY.PyAst.evalUnaryIntFunction
          RangeSumAst.module "sum" n =
        some value := by
  by_cases hn : n <= 0
  · refine ⟨0, ?_⟩
    simp [
      CleanXY.PyAst.evalUnaryIntFunction,
      CleanXY.PyAst.Module.findFunctionBody,
      CleanXY.PyAst.findFunctionBodyIn,
      CleanXY.PyAst.evalIntBlock,
      CleanXY.PyAst.evalBoolExpr,
      CleanXY.PyAst.evalIntExpr,
      CleanXY.PyAst.Env.get?,
      CleanXY.PyAst.evalCmpOp,
      RangeSumAst.module,
      hn,
    ]
  · refine ⟨CleanXY.PyAst.sumRange n.toNat, ?_⟩
    simp [
      CleanXY.PyAst.evalUnaryIntFunction,
      CleanXY.PyAst.Module.findFunctionBody,
      CleanXY.PyAst.findFunctionBodyIn,
      CleanXY.PyAst.evalIntBlock,
      CleanXY.PyAst.evalBoolExpr,
      CleanXY.PyAst.evalIntExpr,
      CleanXY.PyAst.Env.get?,
      CleanXY.PyAst.evalCmpOp,
      RangeSumAst.module,
      hn,
    ]

/-- `sum` never throws for an integer input. -/
theorem sum.«Not Throws» :
    Not (CleanXY.Property.Function.Throws RangeSumAst.module "sum") := by
  rintro ⟨n, exception, hthrow⟩
  by_cases hn : n <= 0
  · simp [
      CleanXY.PyAst.evalUnaryIntFunctionOutcome,
      CleanXY.PyAst.Module.findFunctionBody,
      CleanXY.PyAst.findFunctionBodyIn,
      CleanXY.PyAst.evalIntBlockOutcome,
      CleanXY.PyAst.evalBoolExpr,
      CleanXY.PyAst.evalIntExpr,
      CleanXY.PyAst.Env.get?,
      CleanXY.PyAst.evalCmpOp,
      RangeSumAst.module,
      hn,
    ] at hthrow
  · simp [
      CleanXY.PyAst.evalUnaryIntFunctionOutcome,
      CleanXY.PyAst.Module.findFunctionBody,
      CleanXY.PyAst.findFunctionBodyIn,
      CleanXY.PyAst.evalIntBlockOutcome,
      CleanXY.PyAst.evalBoolExpr,
      CleanXY.PyAst.evalIntExpr,
      CleanXY.PyAst.Env.get?,
      CleanXY.PyAst.evalCmpOp,
      RangeSumAst.module,
      hn,
    ] at hthrow

/-- `sum_naive` returns an integer for every integer input. -/
theorem sum_naive.returns (n : Int) :
    ∃ value,
      CleanXY.PyAst.evalUnaryIntFunction
          RangeSumAst.module "sum_naive" n =
        some value := by
  refine ⟨CleanXY.PyAst.sumRange n.toNat, ?_⟩
  simp [
    CleanXY.PyAst.evalUnaryIntFunction,
    CleanXY.PyAst.Module.findFunctionBody,
    CleanXY.PyAst.findFunctionBodyIn,
    CleanXY.PyAst.evalIntBlock,
    CleanXY.PyAst.evalIntExpr,
    CleanXY.PyAst.evalRangeContribution,
    CleanXY.PyAst.Env.get?,
    RangeSumAst.module,
  ]

/-- `sum_naive` never throws for an integer input. -/
theorem sum_naive.not_throws :
    Not (CleanXY.Property.Function.Throws RangeSumAst.module "sum_naive") := by
  rintro ⟨n, exception, hthrow⟩
  simp [
    CleanXY.PyAst.evalUnaryIntFunctionOutcome,
    CleanXY.PyAst.Module.findFunctionBody,
    CleanXY.PyAst.findFunctionBodyIn,
    CleanXY.PyAst.evalIntBlockOutcome,
    CleanXY.PyAst.evalIntBlock,
    CleanXY.PyAst.evalIntExpr,
    CleanXY.PyAst.evalRangeContribution,
    CleanXY.PyAst.Env.get?,
    RangeSumAst.module,
  ] at hthrow

/-- Neither range-sum implementation can throw for any integer input. -/
theorem noException (n : Int) :
    (∃ value,
      CleanXY.PyAst.evalUnaryIntFunction
          RangeSumAst.module "sum" n =
        some value) ∧
    (∃ value,
      CleanXY.PyAst.evalUnaryIntFunction
          RangeSumAst.module "sum_naive" n =
        some value) :=
  ⟨sum.returns n, sum_naive.returns n⟩

/-- `sum` and `sum_naive` give the same result for every integer input. -/
theorem sum.«Equiv(sum_naive)» :
    CleanXY.Property.Function.Equiv
      RangeSumAst.module "sum" "sum_naive" := by
  intro n
  by_cases hn : n <= 0
  · refine ⟨.ok 0, ?_⟩
    constructor <;> simp [
      CleanXY.PyAst.evalUnaryIntFunctionOutcome,
      CleanXY.PyAst.Module.findFunctionBody,
      CleanXY.PyAst.findFunctionBodyIn,
      CleanXY.PyAst.evalIntBlockOutcome,
      CleanXY.PyAst.evalIntBlock,
      CleanXY.PyAst.evalBoolExpr,
      CleanXY.PyAst.evalIntExpr,
      CleanXY.PyAst.evalRangeContribution,
      CleanXY.PyAst.sumRange,
      CleanXY.PyAst.Env.get?,
      CleanXY.PyAst.evalCmpOp,
      RangeSumAst.module,
      hn,
      Int.toNat_of_nonpos hn,
    ]
  · refine ⟨.ok (CleanXY.PyAst.sumRange n.toNat), ?_⟩
    constructor <;> simp [
      CleanXY.PyAst.evalUnaryIntFunctionOutcome,
      CleanXY.PyAst.Module.findFunctionBody,
      CleanXY.PyAst.findFunctionBodyIn,
      CleanXY.PyAst.evalIntBlockOutcome,
      CleanXY.PyAst.evalIntBlock,
      CleanXY.PyAst.evalBoolExpr,
      CleanXY.PyAst.evalIntExpr,
      CleanXY.PyAst.evalRangeContribution,
      CleanXY.PyAst.Env.get?,
      CleanXY.PyAst.evalCmpOp,
      RangeSumAst.module,
      hn,
    ]

/-- `sum` returns its annotated integer type whenever it does not throw. -/
theorem sum.«ReturnType» :
    CleanXY.Property.Function.ReturnType RangeSumAst.module "sum" := by
  intro n
  obtain ⟨outcome, hsum, _⟩ := sum.«Equiv(sum_naive)» n
  exact ⟨outcome, hsum⟩

/-- The closed-form implementation has constant worst-case cost. -/
theorem sum.«BigO(1)» :
    CleanXY.Property.Function.BigO RangeSumAst.module "sum"
      (.intToNat "n") (fun _ => 1) := by
  apply CleanXY.Property.Function.bigO_of_growth_bound
    (inputSize := .intToNat "n") (growth := .constant)
  · rfl
  · rfl
  · exact CleanXY.PyAst.Growth.constant_isBigO

/-- The loop implementation has linear worst-case cost. -/
theorem sum_naive.«BigO(n)» :
    CleanXY.Property.Function.BigO RangeSumAst.module "sum_naive"
      (.intToNat "n") (fun n => n) := by
  apply CleanXY.Property.Function.bigO_of_growth_bound
    (inputSize := .intToNat "n") (growth := .linear)
  · rfl
  · rfl
  · exact CleanXY.PyAst.Growth.linear_isBigO

end tests.py.range_sum
