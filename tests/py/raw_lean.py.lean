import «.formalsw».tests.py.«raw_lean.py.ast»
import FormalSW

namespace tests.py.raw_lean
open FormalSW.PyAst

theorem module_fact : True := trivial
theorem explicit_fact : True := trivial

theorem g.returns_input (n : Int) : n = n := rfl

theorem g.«Returns» (n : Int) :
    (scalarFunction RawLeanAst.module "g" [.int n]).Returns := ⟨.int n, .done rfl⟩

theorem f.returns_input (n : Int) :
    n = n ∧ RawLeanAst.module.findFunctionBody "f" ≠ none := by
  simp [Module.findFunctionBody, findFunctionBodyIn, RawLeanAst.module]

theorem f.«Returns» (n : Int) :
    (scalarFunction RawLeanAst.module "f" [.int n]).Returns := by
  refine ⟨.int n, Execution.finishes_of_observe (fuel := 1) ?_⟩
  simp [Execution.observe, Execution.observeFrom, scalarFunction, findFunctionIn,
    scalarBlock, executableBody, scalarStep, scalarExpr, argumentEnv, RawLeanAst.module]

theorem f.does_not_throw (n : Int) :
    let this_function := fun (n : Int) => scalarFunction RawLeanAst.module "f" [.int n]
    Not Throws(this_function(n)) :=
  ((Execution.returns_iff_halts_not_throws _).mp (f.«Returns» n)).2

end tests.py.raw_lean
