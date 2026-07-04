import «.leanpy».tests.pass.«range_sum.py.ast»
import LeanPy

namespace Tests.Pass.RangeSum

/-- `sum` returns an integer for every integer input. -/
theorem sum_noThrow (n : Int) :
    ∃ value,
      LeanPy.PyAst.evalUnaryIntFunction
          RangeSumAst.module "sum" n =
        some value := by
  by_cases hn : n <= 0
  · refine ⟨0, ?_⟩
    simp [
      LeanPy.PyAst.evalUnaryIntFunction,
      LeanPy.PyAst.Module.findFunctionBody,
      LeanPy.PyAst.findFunctionBodyIn,
      LeanPy.PyAst.evalIntBlock,
      LeanPy.PyAst.evalBoolExpr,
      LeanPy.PyAst.evalIntExpr,
      LeanPy.PyAst.Env.get?,
      LeanPy.PyAst.evalCmpOp,
      RangeSumAst.module,
      hn,
    ]
  · refine ⟨LeanPy.PyAst.sumRange n.toNat, ?_⟩
    simp [
      LeanPy.PyAst.evalUnaryIntFunction,
      LeanPy.PyAst.Module.findFunctionBody,
      LeanPy.PyAst.findFunctionBodyIn,
      LeanPy.PyAst.evalIntBlock,
      LeanPy.PyAst.evalBoolExpr,
      LeanPy.PyAst.evalIntExpr,
      LeanPy.PyAst.Env.get?,
      LeanPy.PyAst.evalCmpOp,
      RangeSumAst.module,
      hn,
    ]

/-- `sum_naive` returns an integer for every integer input. -/
theorem sumNaive_noThrow (n : Int) :
    ∃ value,
      LeanPy.PyAst.evalUnaryIntFunction
          RangeSumAst.module "sum_naive" n =
        some value := by
  refine ⟨LeanPy.PyAst.sumRange n.toNat, ?_⟩
  simp [
    LeanPy.PyAst.evalUnaryIntFunction,
    LeanPy.PyAst.Module.findFunctionBody,
    LeanPy.PyAst.findFunctionBodyIn,
    LeanPy.PyAst.evalIntBlock,
    LeanPy.PyAst.evalIntExpr,
    LeanPy.PyAst.evalRangeContribution,
    LeanPy.PyAst.Env.get?,
    RangeSumAst.module,
  ]

/-- Neither range-sum implementation can throw for any integer input. -/
theorem noException (n : Int) :
    (∃ value,
      LeanPy.PyAst.evalUnaryIntFunction
          RangeSumAst.module "sum" n =
        some value) ∧
    (∃ value,
      LeanPy.PyAst.evalUnaryIntFunction
          RangeSumAst.module "sum_naive" n =
        some value) :=
  ⟨sum_noThrow n, sumNaive_noThrow n⟩

/-- `sum` and `sum_naive` give the same result for every integer input. -/
theorem sum_equiv_sumNaive (n : Int) :
    LeanPy.PyAst.evalUnaryIntFunction
        RangeSumAst.module "sum" n =
      LeanPy.PyAst.evalUnaryIntFunction
        RangeSumAst.module "sum_naive" n := by
  by_cases hn : n <= 0
  · simp [
      LeanPy.PyAst.evalUnaryIntFunction,
      LeanPy.PyAst.Module.findFunctionBody,
      LeanPy.PyAst.findFunctionBodyIn,
      LeanPy.PyAst.evalIntBlock,
      LeanPy.PyAst.evalBoolExpr,
      LeanPy.PyAst.evalIntExpr,
      LeanPy.PyAst.evalRangeContribution,
      LeanPy.PyAst.sumRange,
      LeanPy.PyAst.Env.get?,
      LeanPy.PyAst.evalCmpOp,
      RangeSumAst.module,
      hn,
      Int.toNat_of_nonpos hn,
    ]
  · simp [
      LeanPy.PyAst.evalUnaryIntFunction,
      LeanPy.PyAst.Module.findFunctionBody,
      LeanPy.PyAst.findFunctionBodyIn,
      LeanPy.PyAst.evalIntBlock,
      LeanPy.PyAst.evalBoolExpr,
      LeanPy.PyAst.evalIntExpr,
      LeanPy.PyAst.evalRangeContribution,
      LeanPy.PyAst.Env.get?,
      LeanPy.PyAst.evalCmpOp,
      RangeSumAst.module,
      hn,
    ]

end Tests.Pass.RangeSum
