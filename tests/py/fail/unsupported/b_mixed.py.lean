import «.formalsw».tests.py.fail.unsupported.«b_mixed.py.ast»
import FormalSW

namespace tests.py.fail.unsupported.b_mixed
open FormalSW.PyAst

theorem identity.«Returns» (n : Int) :
    (scalarFunction BMixedAst.module "identity" [.int n]).Returns := by
  exact ⟨.int n, .done rfl⟩

end tests.py.fail.unsupported.b_mixed
