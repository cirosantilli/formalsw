import «.cleanxy».lang.py.builtin.type.«dictview.py.ast»
import lang.py.builtin.type.dictview

namespace lang.py.builtin.type.dictview

open CleanXY.PyAst

theorem modeled :
    DictviewAst.module.hasExactlyClassMethods "dict_keys" ["__init__", "__iter__", "__len__"] = true ∧
    DictviewAst.module.hasExactlyClassMethods "dict_values" ["__init__", "__iter__", "__len__"] = true ∧
    DictviewAst.module.hasExactlyClassMethods "dict_items" ["__init__", "__iter__", "__len__"] = true := by
  decide

theorem source_fingerprint : DictviewAst.module.fingerprint = 1558093408199490595 := by
  native_decide

end lang.py.builtin.type.dictview
