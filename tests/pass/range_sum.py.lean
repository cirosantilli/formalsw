import «.cleanxyz».tests.pass.«range_sum.py.ast»
import CleanXYZ

namespace tests.pass.range_sum

/-- `sum` returns an integer for every integer input. -/
theorem sum.returns (n : Int) :
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
theorem sum.«Not Throws» :
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
theorem sum_naive.returns (n : Int) :
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
theorem sum_naive.not_throws :
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
  ⟨sum.returns n, sum_naive.returns n⟩

/-- `sum` and `sum_naive` give the same result for every integer input. -/
theorem sum.«Equiv(sum_naive)» :
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

/-- The closed-form implementation has constant worst-case cost. -/
theorem sum.«BigO(1, n = n)» :
    CleanXYZ.Property.Function.BigO RangeSumAst.module "sum"
      (.intToNat "n") (fun _ => 1) := by
  apply CleanXYZ.Property.Function.bigO_of_growth_bound
    (inputSize := .intToNat "n") (growth := .constant)
  · rfl
  · rfl
  · exact CleanXYZ.PyAst.Growth.constant_isBigO

/-- The loop implementation has linear worst-case cost. -/
theorem sum_naive.«BigO(n, n = n)» :
    CleanXYZ.Property.Function.BigO RangeSumAst.module "sum_naive"
      (.intToNat "n") (fun n => n) := by
  apply CleanXYZ.Property.Function.bigO_of_growth_bound
    (inputSize := .intToNat "n") (growth := .linear)
  · rfl
  · rfl
  · exact CleanXYZ.PyAst.Growth.linear_isBigO

end tests.pass.range_sum
