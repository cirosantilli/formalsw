import «.cleanxyz».tests.pass.«range_sum.py.ast»
import CleanXYZ

namespace Tests.Pass.RangeSum

/-- `sum` returns an integer for every integer input. -/
theorem sum_noThrow (n : Int) :
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

/-- `sum_naive` returns an integer for every integer input. -/
theorem sumNaive_noThrow (n : Int) :
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
  ⟨sum_noThrow n, sumNaive_noThrow n⟩

/-- `sum` and `sum_naive` give the same result for every integer input. -/
theorem sum_equiv_sumNaive (n : Int) :
    CleanXYZ.PyAst.evalUnaryIntFunction
        RangeSumAst.module "sum" n =
      CleanXYZ.PyAst.evalUnaryIntFunction
        RangeSumAst.module "sum_naive" n := by
  by_cases hn : n <= 0
  · simp [
      CleanXYZ.PyAst.evalUnaryIntFunction,
      CleanXYZ.PyAst.Module.findFunctionBody,
      CleanXYZ.PyAst.findFunctionBodyIn,
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
  · simp [
      CleanXYZ.PyAst.evalUnaryIntFunction,
      CleanXYZ.PyAst.Module.findFunctionBody,
      CleanXYZ.PyAst.findFunctionBodyIn,
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
