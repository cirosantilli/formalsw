import «.cleanxy».tests.py.«equiv_throw.py.ast»
import CleanXY

namespace tests.py.equiv_throw

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

/-- The functions throw exception objects with different messages. -/
theorem throw_msg_1.«Not Equiv(throw_msg_2)» :
    Not (CleanXY.Property.Function.Equiv
      EquivThrowAst.module "throw_msg_1" "throw_msg_2") := by
  intro equivalent
  obtain ⟨outcome, left, right⟩ := equivalent 0
  simp [
    CleanXY.PyAst.evalUnaryIntFunctionOutcome,
    CleanXY.PyAst.Module.findFunctionBody,
    CleanXY.PyAst.findFunctionBodyIn,
    CleanXY.PyAst.evalIntBlockOutcome,
    CleanXY.PyAst.evalExceptionObject,
    CleanXY.PyAst.evalExceptionArg,
    EquivThrowAst.module,
  ] at left right
  rw [← left] at right
  simp at right

end tests.py.equiv_throw
