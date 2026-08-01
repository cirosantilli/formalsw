import «.cleanxy».lang.py.builtin.«str.py.ast»
import CleanXY

namespace lang.py.builtin.str

/-- The Python definition has the expected code-point payload and comparisons. -/
theorem modeled :
    StrAst.module.isCodepointStringClass "str" = true := by
  rfl

end lang.py.builtin.str
