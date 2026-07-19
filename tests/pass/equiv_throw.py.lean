import «.cleanxyz».tests.pass.«equiv_throw.py.ast»
import CleanXYZ

namespace Tests.Pass.EquivThrow

/-- Both implementations return and throw equivalent objects for every input. -/
theorem doubleOrThrow.equiv_doubleOrThrowAlt :
    CleanXYZ.Property.Function.Equiv
      EquivThrowAst.module "double_or_throw" "double_or_throw_alt" := by
  intro n
  by_cases even : n % 2 = 0
  · refine ⟨.ok (n * 2), ?_⟩
    constructor <;> simp [
      CleanXYZ.PyAst.evalUnaryIntFunctionOutcome,
      CleanXYZ.PyAst.Module.findFunctionBody,
      CleanXYZ.PyAst.findFunctionBodyIn,
      CleanXYZ.PyAst.evalIntBlockOutcome,
      CleanXYZ.PyAst.evalBoolExpr,
      CleanXYZ.PyAst.evalIntExpr,
      CleanXYZ.PyAst.Env.get?,
      CleanXYZ.PyAst.evalCmpOp,
      EquivThrowAst.module,
      even,
    ]
  · refine ⟨.error {
      typeName := "ValueError"
      args := [.string "odd input", .int n]
    }, ?_⟩
    constructor <;> simp [
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
      EquivThrowAst.module,
      even,
    ]

end Tests.Pass.EquivThrow
