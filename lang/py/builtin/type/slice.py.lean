import «.cleanxy».lang.py.builtin.type.«slice.py.ast»
import lang.py.builtin.type.slice

namespace lang.py.builtin.type.slice

open CleanXY.PyAst

theorem modeled :
    SliceAst.module.hasExactlyClassMethods "slice" ["__init__"] = true := by
  rfl

theorem source_fingerprint : SliceAst.module.fingerprint = 18103686344632525824 := by
  native_decide

end lang.py.builtin.type.slice
