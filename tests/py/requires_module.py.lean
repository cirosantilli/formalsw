import «.formalsw».tests.py.«requires_module.py.ast»
import FormalSW

namespace tests.py.requires_module
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := RequiresModuleAst.module
private abbrev moduleDomain := Condition program (fun _ => none) RequiresModuleAst.requires_module_0
private abbrev domain (n : Int) := Condition program
  (fun key => if key = "n" then some (.int n) else none) RequiresModuleAst.requires_identity_0

theorem established (_hp : moduleDomain) : True := .intro

theorem identity.«Returns» (n : Int) (_hm : moduleDomain) (_hp : domain n) :
    (scalarFunction program "identity" [.int n]).Returns := ⟨.int n, .done rfl⟩

theorem identity.valid (n : Int) (hp : moduleDomain ∧ domain n) : n ≥ 0 := by
  simpa [evalCmpOp] using Evaluates.condition_int_compare hp.2 rfl

theorem no_domain.«Not Throws» : ¬ (moduleDomain ∧
    Condition program (fun _ => none) RequiresModuleAst.requires_no_domain_0 ∧
    (scalarFunction program "no_domain" []).Throws) := by
  rintro ⟨_, hp, _⟩
  have run : Evaluates program (fun _ => none) RequiresModuleAst.requires_no_domain_0 (.bool false) :=
    Evaluates.constant
  cases run.condition_iff.mp hp

end tests.py.requires_module
