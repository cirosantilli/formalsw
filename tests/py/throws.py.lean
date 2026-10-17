import «.formalsw».tests.py.«throws.py.ast»
import FormalSW

namespace tests.py.throws

open FormalSW.PyAst

private theorem reject_odd_outcome (n : Int) :
    (scalarFunction ThrowsAst.module "reject_odd" [.int n]).observe 2 =
      .done (if n % 2 = 0 then .ok (.int n)
        else .error { typeName := "ValueError", args := [.string "odd input"] }) := by
  by_cases even : n % 2 = 0 <;>
    simp [Execution.observe, Execution.observeFrom, scalarFunction, findFunctionIn,
      scalarBlock, executableBody, scalarStep, scalarExpr, scalarCompare, evalCmpOp, scalarBinary,
      scalarTruth, scalarException, argumentEnv, ThrowsAst.module, even]

theorem reject_odd.«Halts» (n : Int) :
    (scalarFunction ThrowsAst.module "reject_odd" [.int n]).Halts :=
  ⟨_, Execution.finishes_of_observe (reject_odd_outcome n)⟩

theorem reject_odd.throws_at_one :
    let this_function := fun (n : Int) => scalarFunction ThrowsAst.module "reject_odd" [.int n]
    Throws(this_function(1)) := by
  exact ⟨_, Execution.finishes_of_observe (reject_odd_outcome 1)⟩

theorem reject_odd.«Throws» :
    FormalSW.Property.Function.Throws ThrowsAst.module "reject_odd" :=
  ⟨1, reject_odd.throws_at_one⟩

theorem reject_odd.returns_at_zero :
    let this_function := fun (n : Int) => scalarFunction ThrowsAst.module "reject_odd" [.int n]
    Returns(this_function(0)) := by
  exact ⟨_, Execution.finishes_of_observe (reject_odd_outcome 0)⟩

end tests.py.throws
