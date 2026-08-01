import «.cleanxy».lang.py.builtin.type.«dict.py.ast»
import lang.py.builtin.type.dict

namespace lang.py.builtin.type.dict

open CleanXY.PyAst

theorem modeled :
    DictAst.module.hasExactlyClassMethods "dict"
      ["__init__", "__len__", "__contains__", "__getitem__", "__setitem__", "__delitem__", "clear", "copy", "keys"] = true := by
  rfl

theorem source_fingerprint : DictAst.module.fingerprint = 11058859598762953261 := by
  native_decide

theorem insertion_order_equivalent (value : CleanXY.Py.Builtin.Dict.Dict α β cmp) :
    CleanXY.Py.Builtin.Dict.keys value = value.order := by
  rfl

end lang.py.builtin.type.dict
