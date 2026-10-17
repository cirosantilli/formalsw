import «.formalsw».lang.py.builtin.type.«set.py.ast»
import lang.py.builtin.type.set

namespace lang.py.builtin.type.set

open FormalSW.PyAst

theorem modeled :
    SetAst.module.hasExactlyClassMethods "set"
      ["__init__", "__len__", "__contains__", "add", "discard", "clear", "copy"] = true ∧
    SetAst.module.hasExactlyClassMethods "frozenset"
      ["__init__", "__len__", "__contains__", "copy"] = true := by
  decide

theorem source_fingerprint : SetAst.module.fingerprint = 9047637200955768486 := by
  native_decide

end lang.py.builtin.type.set
