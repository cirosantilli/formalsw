import «.cleanxyz».tests.pass.«nothrow.py.ast»
import CleanXYZ

namespace Tests.Pass.Nothrow

/-- `reject_odd` does not successfully evaluate for every integer input. -/
theorem reject_odd_not_noThrow :
    ¬ CleanXYZ.Property.Function.NoThrow NothrowAst.module "reject_odd" := by
  intro noThrow
  obtain ⟨value, hvalue⟩ := noThrow 1
  simp [
    CleanXYZ.PyAst.evalUnaryIntFunction,
    CleanXYZ.PyAst.Module.findFunctionBody,
    CleanXYZ.PyAst.findFunctionBodyIn,
    CleanXYZ.PyAst.evalIntBlock,
    CleanXYZ.PyAst.evalBoolExpr,
    CleanXYZ.PyAst.evalIntExpr,
    CleanXYZ.PyAst.Env.get?,
    CleanXYZ.PyAst.evalCmpOp,
    NothrowAst.module,
  ] at hvalue

end Tests.Pass.Nothrow
