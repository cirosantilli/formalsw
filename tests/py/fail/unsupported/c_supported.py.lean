import «.formalsw».tests.py.fail.unsupported.«c_supported.py.ast»
import FormalSW

namespace tests.py.fail.unsupported.c_supported
open FormalSW.PyAst

theorem identity.«Returns» (n : Int) :
    (scalarFunction CSupportedAst.module "identity" [.int n]).Returns := by
  exact ⟨.int n, .done rfl⟩

end tests.py.fail.unsupported.c_supported
