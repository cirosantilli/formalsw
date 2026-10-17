import «.cleanxy».tests.py.«typing.py.ast»
import CleanXY

namespace tests.py.typing

/-- An unrestricted comparison can receive incompatible runtime types. -/
theorem lt_untyped.«Throws» :
    CleanXY.Property.Function.Throws TypingAst.module "lt_untyped" := by
  refine ⟨.int 0, .string [], { typeName := "TypeError", args := [] }, ?_⟩
  constructor
  · rfl
  constructor
  · rfl
  · rfl

open CleanXY.PyAst

/-- Evaluating the comparison and falling off the end returns Python None. -/
theorem lt_int.«Returns» (a b : Int) :
    (scalarFunction TypingAst.module "lt_int" [.int a, .int b]).Returns := by
  refine ⟨.none, Execution.finishes_of_observe (fuel := 2) ?_⟩
  simp [Execution.observe, Execution.observeFrom, scalarFunction, findFunctionIn,
    scalarBlock, executableBody, scalarStep, scalarExpr, scalarCompare,
    argumentEnv, List.lookup, evalCmpOp, TypingAst.module]

theorem lt_str.«Returns» (a b : String) :
    (scalarFunction TypingAst.module "lt_str" [.string a, .string b]).Returns := by
  refine ⟨.none, Execution.finishes_of_observe (fuel := 2) ?_⟩
  simp [Execution.observe, Execution.observeFrom, scalarFunction, findFunctionIn,
    scalarBlock, executableBody, scalarStep, scalarExpr, scalarCompare,
    argumentEnv, List.lookup, TypingAst.module]

end tests.py.typing
