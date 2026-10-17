import «.formalsw».lang.py.builtin.type.«str.py.ast»
import FormalSW

namespace lang.py.builtin.type.str

/-- The Python definition has the expected code-point payload and comparisons. -/
theorem modeled :
    StrAst.module.isCodepointStringClass "str" = true := by
  rfl

theorem source_fingerprint : StrAst.module.fingerprint = 2339401588560382508 := by
  native_decide

theorem length_equivalent (value : FormalSW.Py.Builtin.Str.Str) :
    FormalSW.Py.Builtin.Str.size value = value.length := by
  rfl

end lang.py.builtin.type.str
