import «.cleanxyz».tests.pass.«throws.py.ast»
import CleanXYZ

namespace Tests.Pass.Throws

/-- `reject_odd` throws for at least one integer input. -/
theorem rejectOdd_throws :
    CleanXYZ.Property.Function.Throws ThrowsAst.module "reject_odd" := by
  refine ⟨1, ?_⟩
  simp [
    CleanXYZ.PyAst.evalUnaryIntFunction,
    CleanXYZ.PyAst.Module.findFunctionBody,
    CleanXYZ.PyAst.findFunctionBodyIn,
    CleanXYZ.PyAst.evalIntBlock,
    CleanXYZ.PyAst.evalBoolExpr,
    CleanXYZ.PyAst.evalIntExpr,
    CleanXYZ.PyAst.Env.get?,
    CleanXYZ.PyAst.evalCmpOp,
    ThrowsAst.module,
  ]

end Tests.Pass.Throws
