import «.formalsw».lang.py.builtin.type.«dict.py.ast»
import lang.py.builtin.type.dict

namespace lang.py.builtin.type.dict

open FormalSW.PyAst

theorem modeled :
    DictAst.module.hasExactlyClassMethods "dict"
      ["__init__", "__len__", "__contains__", "__getitem__", "__setitem__", "__delitem__", "clear", "copy", "keys"] = true := by
  rfl

theorem source_fingerprint : DictAst.module.fingerprint = 13275742418967923092 := by
  native_decide

theorem insertion_order_equivalent (value : FormalSW.Py.Builtin.Dict.Dict α β cmp) :
    FormalSW.Py.Builtin.Dict.keys value = value.order := by
  rfl

end lang.py.builtin.type.dict
