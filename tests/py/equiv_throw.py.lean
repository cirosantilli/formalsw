import «.cleanxy».tests.py.«equiv_throw.py.ast»
import CleanXY

namespace tests.py.equiv_throw

open CleanXY.PyAst

/-- Matching bodies have matching finite normal and exceptional executions. -/
theorem double_or_throw.«Equiv(double_or_throw_alt)» :
    CleanXY.Property.Function.Equiv
      EquivThrowAst.module "double_or_throw" "double_or_throw_alt" := by
  intro n outcome
  rfl

/-- Structurally different exception objects are different outcomes. -/
theorem throw_msg_1.«Not Equiv(throw_msg_2)» :
    Not (CleanXY.Property.Function.Equiv
      EquivThrowAst.module "throw_msg_1" "throw_msg_2") := by
  intro equivalent
  have left : Finishes (scalarFunction EquivThrowAst.module "throw_msg_1" [.int 0]).step
      (scalarFunction EquivThrowAst.module "throw_msg_1" [.int 0]).initial
      (.error ⟨"Exception", [.string "msg1"]⟩) := .done rfl
  have right : Finishes (scalarFunction EquivThrowAst.module "throw_msg_2" [.int 0]).step
      (scalarFunction EquivThrowAst.module "throw_msg_2" [.int 0]).initial
      (.error ⟨"Exception", [.string "msg2"]⟩) := .done rfl
  have impossible := ((equivalent 0 _).mp left).unique right
  simp at impossible


theorem double_or_throw_alt.«Halts» (n : Int) :
    (scalarFunction EquivThrowAst.module "double_or_throw_alt" [.int n]).Halts := by
  refine ⟨if n % 2 = 0 then .ok (.int (n * 2))
    else .error ⟨"ValueError", [.string "odd input", .int n]⟩,
    Execution.finishes_of_observe (fuel := 2) ?_⟩
  by_cases even : n % 2 = 0 <;>
    simp [Execution.observe, Execution.observeFrom, scalarFunction, findFunctionIn,
      scalarBlock, executableBody, scalarStep, scalarExpr, scalarCompare, evalCmpOp, scalarBinary,
      scalarTruth, scalarException, argumentEnv, EquivThrowAst.module, even]

theorem throw_msg_1.«Halts» (n : Int) :
    (scalarFunction EquivThrowAst.module "throw_msg_1" [.int n]).Halts :=
  ⟨.error ⟨"Exception", [.string "msg1"]⟩, .done rfl⟩

theorem throw_msg_2.«Halts» (n : Int) :
    (scalarFunction EquivThrowAst.module "throw_msg_2" [.int n]).Halts :=
  ⟨.error ⟨"Exception", [.string "msg2"]⟩, .done rfl⟩

/-- Halts follows from the reference implementation through Equiv. -/
example (n : Int) : (scalarFunction EquivThrowAst.module "double_or_throw" [.int n]).Halts :=
  (double_or_throw.«Equiv(double_or_throw_alt)» n).halts_iff.mpr (double_or_throw_alt.«Halts» n)

end tests.py.equiv_throw
