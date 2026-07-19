import «.cleanxy».tests.pass.«equiv_throw.py.ast»
import CleanXY

namespace tests.pass.equiv_throw

/-- Both implementations return and throw equivalent objects for every input. -/
theorem double_or_throw.«Equiv(double_or_throw_alt)» :
    CleanXY.Property.Function.Equiv
      EquivThrowAst.module "double_or_throw" "double_or_throw_alt" := by
  intro n
  by_cases even : n % 2 = 0
  · refine ⟨.ok (n * 2), ?_⟩
    constructor <;> simp [
      CleanXY.PyAst.evalUnaryIntFunctionOutcome,
      CleanXY.PyAst.Module.findFunctionBody,
      CleanXY.PyAst.findFunctionBodyIn,
      CleanXY.PyAst.evalIntBlockOutcome,
      CleanXY.PyAst.evalBoolExpr,
      CleanXY.PyAst.evalIntExpr,
      CleanXY.PyAst.Env.get?,
      CleanXY.PyAst.evalCmpOp,
      EquivThrowAst.module,
      even,
    ]
  · refine ⟨.error {
      typeName := "ValueError"
      args := [.string "odd input", .int n]
    }, ?_⟩
    constructor <;> simp [
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
      EquivThrowAst.module,
      even,
    ]

end tests.pass.equiv_throw
