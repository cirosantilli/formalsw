import «.cleanxy».tests.py.fail.unsupported.«c_supported.py.ast»
import CleanXY

namespace tests.py.fail.unsupported.c_supported
open CleanXY.PyAst

theorem identity.«Returns» (n : Int) :
    (scalarFunction CSupportedAst.module "identity" [.int n]).Returns := by
  exact ⟨.int n, .done rfl⟩

end tests.py.fail.unsupported.c_supported
