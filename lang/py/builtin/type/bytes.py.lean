import «.formalsw».lang.py.builtin.type.«bytes.py.ast»
import lang.py.builtin.type.bytes

namespace lang.py.builtin.type.bytes

open FormalSW.PyAst

theorem modeled :
    BytesAst.module.hasExactlyClassMethods "bytes"
      ["__init__", "__eq__", "__lt__", "__le__", "__gt__", "__ge__", "__len__", "__getitem__"] = true := by
  rfl

theorem source_fingerprint : BytesAst.module.fingerprint = 13820953856544055677 := by
  native_decide

theorem length_equivalent (value : FormalSW.Py.Builtin.Bytes.ByteString) :
    FormalSW.Py.Builtin.Bytes.size value = value.length := by
  rfl

end lang.py.builtin.type.bytes
