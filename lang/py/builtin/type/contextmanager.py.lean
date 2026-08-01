import «.cleanxy».lang.py.builtin.type.«contextmanager.py.ast»
import lang.py.builtin.type.contextmanager

namespace lang.py.builtin.type.contextmanager

open CleanXY.PyAst

theorem modeled :
    ContextmanagerAst.module.hasExactlyClassMethods "contextmanager"
      ["__init__", "__enter__", "__exit__"] = true := by
  rfl

theorem source_fingerprint : ContextmanagerAst.module.fingerprint = 2344344226781193825 := by
  native_decide

end lang.py.builtin.type.contextmanager
