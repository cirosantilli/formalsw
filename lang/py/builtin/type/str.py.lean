import «.cleanxy».lang.py.builtin.type.«str.py.ast»
import CleanXY

namespace lang.py.builtin.type.str

/-- The Python definition has the expected code-point payload and comparisons. -/
theorem modeled :
    StrAst.module.isCodepointStringClass "str" = true := by
  rfl

theorem source_fingerprint : StrAst.module.fingerprint = 5533158025547653472 := by
  native_decide

theorem length_equivalent (value : CleanXY.Py.Builtin.Str.Str) :
    CleanXY.Py.Builtin.Str.size value = value.length := by
  rfl

end lang.py.builtin.type.str
