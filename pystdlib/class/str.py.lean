import «.cleanxy».pystdlib.«class».«str.py.ast»
import CleanXY

namespace pystdlibClassStr

/-- The Python definition has the expected code-point payload and comparisons. -/
theorem modeled :
    StrAst.module.isCodepointStringClass "str" = true := by
  rfl

end pystdlibClassStr
