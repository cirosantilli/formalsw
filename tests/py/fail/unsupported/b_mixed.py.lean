import «.cleanxy».tests.py.fail.unsupported.«b_mixed.py.ast»
import CleanXY

namespace tests.py.fail.unsupported.b_mixed
open CleanXY.PyAst

theorem identity.«Returns» (n : Int) :
    (scalarFunction BMixedAst.module "identity" [.int n]).Returns := by
  exact ⟨.int n, .done rfl⟩

end tests.py.fail.unsupported.b_mixed
