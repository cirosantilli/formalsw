import «.cleanxyz».tests.pass.«range_sum.py.ast»
import CleanXYZ

namespace Tests.Pass.RangeSum

/-- `sum` returns an integer for every integer input. -/
theorem sum_returns (n : Int) :
    ∃ value,
      CleanXYZ.PyAst.evalUnaryIntFunction
          RangeSumAst.module "sum" n =
        some value := by
  by_cases hn : n <= 0
  · refine ⟨0, ?_⟩
    simp [
      CleanXYZ.PyAst.evalUnaryIntFunction,
      CleanXYZ.PyAst.Module.findFunctionBody,
      CleanXYZ.PyAst.findFunctionBodyIn,
      CleanXYZ.PyAst.evalIntBlock,
      CleanXYZ.PyAst.evalBoolExpr,
      CleanXYZ.PyAst.evalIntExpr,
      CleanXYZ.PyAst.Env.get?,
      CleanXYZ.PyAst.evalCmpOp,
      RangeSumAst.module,
      hn,
    ]
  · refine ⟨CleanXYZ.PyAst.sumRange n.toNat, ?_⟩
    simp [
      CleanXYZ.PyAst.evalUnaryIntFunction,
      CleanXYZ.PyAst.Module.findFunctionBody,
      CleanXYZ.PyAst.findFunctionBodyIn,
      CleanXYZ.PyAst.evalIntBlock,
      CleanXYZ.PyAst.evalBoolExpr,
      CleanXYZ.PyAst.evalIntExpr,
      CleanXYZ.PyAst.Env.get?,
      CleanXYZ.PyAst.evalCmpOp,
      RangeSumAst.module,
      hn,
    ]

/-- `sum` never throws for an integer input. -/
theorem sum_not_throws :
    Not (CleanXYZ.Property.Function.Throws RangeSumAst.module "sum") := by
  rintro ⟨n, exception, hthrow⟩
  by_cases hn : n <= 0
  · simp [
      CleanXYZ.PyAst.evalUnaryIntFunctionOutcome,
      CleanXYZ.PyAst.Module.findFunctionBody,
      CleanXYZ.PyAst.findFunctionBodyIn,
      CleanXYZ.PyAst.evalIntBlockOutcome,
      CleanXYZ.PyAst.evalBoolExpr,
      CleanXYZ.PyAst.evalIntExpr,
      CleanXYZ.PyAst.Env.get?,
      CleanXYZ.PyAst.evalCmpOp,
      RangeSumAst.module,
      hn,
    ] at hthrow
  · simp [
      CleanXYZ.PyAst.evalUnaryIntFunctionOutcome,
      CleanXYZ.PyAst.Module.findFunctionBody,
      CleanXYZ.PyAst.findFunctionBodyIn,
      CleanXYZ.PyAst.evalIntBlockOutcome,
      CleanXYZ.PyAst.evalBoolExpr,
      CleanXYZ.PyAst.evalIntExpr,
      CleanXYZ.PyAst.Env.get?,
      CleanXYZ.PyAst.evalCmpOp,
      RangeSumAst.module,
      hn,
    ] at hthrow

/-- `sum_naive` returns an integer for every integer input. -/
theorem sumNaive_returns (n : Int) :
    ∃ value,
      CleanXYZ.PyAst.evalUnaryIntFunction
          RangeSumAst.module "sum_naive" n =
        some value := by
  refine ⟨CleanXYZ.PyAst.sumRange n.toNat, ?_⟩
  simp [
    CleanXYZ.PyAst.evalUnaryIntFunction,
    CleanXYZ.PyAst.Module.findFunctionBody,
    CleanXYZ.PyAst.findFunctionBodyIn,
    CleanXYZ.PyAst.evalIntBlock,
    CleanXYZ.PyAst.evalIntExpr,
    CleanXYZ.PyAst.evalRangeContribution,
    CleanXYZ.PyAst.Env.get?,
    RangeSumAst.module,
  ]

/-- `sum_naive` never throws for an integer input. -/
theorem sumNaive_not_throws :
    Not (CleanXYZ.Property.Function.Throws RangeSumAst.module "sum_naive") := by
  rintro ⟨n, exception, hthrow⟩
  simp [
    CleanXYZ.PyAst.evalUnaryIntFunctionOutcome,
    CleanXYZ.PyAst.Module.findFunctionBody,
    CleanXYZ.PyAst.findFunctionBodyIn,
    CleanXYZ.PyAst.evalIntBlockOutcome,
    CleanXYZ.PyAst.evalIntBlock,
    CleanXYZ.PyAst.evalIntExpr,
    CleanXYZ.PyAst.evalRangeContribution,
    CleanXYZ.PyAst.Env.get?,
    RangeSumAst.module,
  ] at hthrow

/-- Neither range-sum implementation can throw for any integer input. -/
theorem noException (n : Int) :
    (∃ value,
      CleanXYZ.PyAst.evalUnaryIntFunction
          RangeSumAst.module "sum" n =
        some value) ∧
    (∃ value,
      CleanXYZ.PyAst.evalUnaryIntFunction
          RangeSumAst.module "sum_naive" n =
        some value) :=
  ⟨sum_returns n, sumNaive_returns n⟩

/-- `sum` and `sum_naive` give the same result for every integer input. -/
theorem sum_equiv_sumNaive :
    CleanXYZ.Property.Function.Equiv
      RangeSumAst.module "sum" "sum_naive" := by
  intro n
  by_cases hn : n <= 0
  · refine ⟨.ok 0, ?_⟩
    constructor <;> simp [
      CleanXYZ.PyAst.evalUnaryIntFunctionOutcome,
      CleanXYZ.PyAst.Module.findFunctionBody,
      CleanXYZ.PyAst.findFunctionBodyIn,
      CleanXYZ.PyAst.evalIntBlockOutcome,
      CleanXYZ.PyAst.evalIntBlock,
      CleanXYZ.PyAst.evalBoolExpr,
      CleanXYZ.PyAst.evalIntExpr,
      CleanXYZ.PyAst.evalRangeContribution,
      CleanXYZ.PyAst.sumRange,
      CleanXYZ.PyAst.Env.get?,
      CleanXYZ.PyAst.evalCmpOp,
      RangeSumAst.module,
      hn,
      Int.toNat_of_nonpos hn,
    ]
  · refine ⟨.ok (CleanXYZ.PyAst.sumRange n.toNat), ?_⟩
    constructor <;> simp [
      CleanXYZ.PyAst.evalUnaryIntFunctionOutcome,
      CleanXYZ.PyAst.Module.findFunctionBody,
      CleanXYZ.PyAst.findFunctionBodyIn,
      CleanXYZ.PyAst.evalIntBlockOutcome,
      CleanXYZ.PyAst.evalIntBlock,
      CleanXYZ.PyAst.evalBoolExpr,
      CleanXYZ.PyAst.evalIntExpr,
      CleanXYZ.PyAst.evalRangeContribution,
      CleanXYZ.PyAst.Env.get?,
      CleanXYZ.PyAst.evalCmpOp,
      RangeSumAst.module,
      hn,
    ]

end Tests.Pass.RangeSum
