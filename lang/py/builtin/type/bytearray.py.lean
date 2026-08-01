import «.cleanxy».lang.py.builtin.type.«bytearray.py.ast»
import lang.py.builtin.type.bytearray

namespace lang.py.builtin.type.bytearray

open CleanXY.PyAst

theorem modeled :
    BytearrayAst.module.hasExactlyClassMethods "bytearray"
      ["__init__", "__len__", "__getitem__", "append", "clear", "extend", "reverse"] = true := by
  rfl

theorem source_fingerprint : BytearrayAst.module.fingerprint = 9233497824801365712 := by
  native_decide

theorem append_equivalent (value : CleanXY.Py.Builtin.ByteArray.ByteArray) (byte : UInt8) :
    CleanXY.Py.Builtin.ByteArray.append value byte = value ++ [byte] := by
  rfl

end lang.py.builtin.type.bytearray
