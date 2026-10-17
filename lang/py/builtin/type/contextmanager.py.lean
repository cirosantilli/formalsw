import «.formalsw».lang.py.builtin.type.«contextmanager.py.ast»
import lang.py.builtin.type.contextmanager

namespace lang.py.builtin.type.contextmanager

open FormalSW.PyAst

theorem modeled :
    ContextmanagerAst.module.hasExactlyClassMethods "contextmanager"
      ["__init__", "__enter__", "__exit__"] = true := by
  rfl

theorem source_fingerprint : ContextmanagerAst.module.fingerprint = 129784840927964959 := by
  native_decide

end lang.py.builtin.type.contextmanager
