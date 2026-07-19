import «.cleanxy».tests.«throws.py.ast»
import CleanXY

namespace tests.throws

/-- `reject_odd` throws for at least one integer input. -/
theorem reject_odd.«Throws» :
    CleanXY.Property.Function.Throws ThrowsAst.module "reject_odd" := by
  refine ⟨1, { typeName := "ValueError", args := [.string "odd input"] }, ?_⟩
  simp [
    CleanXY.PyAst.evalUnaryIntFunctionOutcome,
    CleanXY.PyAst.Module.findFunctionBody,
    CleanXY.PyAst.findFunctionBodyIn,
    CleanXY.PyAst.evalIntBlockOutcome,
    CleanXY.PyAst.evalBoolExpr,
    CleanXY.PyAst.evalIntExpr,
    CleanXY.PyAst.evalExceptionObject,
    CleanXY.PyAst.evalExceptionArg,
    CleanXY.PyAst.Env.get?,
    CleanXY.PyAst.evalCmpOp,
    ThrowsAst.module,
  ]

end tests.throws
