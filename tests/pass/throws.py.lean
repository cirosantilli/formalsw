import «.cleanxyz».tests.pass.«throws.py.ast»
import CleanXYZ

namespace Tests.Pass.Throws

/-- `reject_odd` throws for at least one integer input. -/
theorem rejectOdd.throws :
    CleanXYZ.Property.Function.Throws ThrowsAst.module "reject_odd" := by
  refine ⟨1, { typeName := "ValueError", args := [.string "odd input"] }, ?_⟩
  simp [
    CleanXYZ.PyAst.evalUnaryIntFunctionOutcome,
    CleanXYZ.PyAst.Module.findFunctionBody,
    CleanXYZ.PyAst.findFunctionBodyIn,
    CleanXYZ.PyAst.evalIntBlockOutcome,
    CleanXYZ.PyAst.evalBoolExpr,
    CleanXYZ.PyAst.evalIntExpr,
    CleanXYZ.PyAst.evalExceptionObject,
    CleanXYZ.PyAst.evalExceptionArg,
    CleanXYZ.PyAst.Env.get?,
    CleanXYZ.PyAst.evalCmpOp,
    ThrowsAst.module,
  ]

end Tests.Pass.Throws
