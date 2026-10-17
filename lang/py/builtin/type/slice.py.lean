import «.formalsw».lang.py.builtin.type.«slice.py.ast»
import lang.py.builtin.type.slice

namespace lang.py.builtin.type.slice

open FormalSW.PyAst

theorem modeled :
    SliceAst.module.hasExactlyClassMethods "slice" ["__init__"] = true := by
  rfl

theorem source_fingerprint : SliceAst.module.fingerprint = 13788410798301299466 := by
  native_decide

end lang.py.builtin.type.slice
