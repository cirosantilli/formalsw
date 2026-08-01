import «.cleanxy».lang.py.builtin.type.«bool.py.ast»
import lang.py.builtin.type.bool

namespace lang.py.builtin.type.bool

open CleanXY.PyAst
open CleanXY.Py.Builtin

theorem modeled :
    BoolAst.module.hasExactlyClassMethods "bool"
      ["__init__", "__bool__", "__int__", "__index__", "__eq__", "__hash__"] = true := by
  rfl

theorem source_fingerprint : BoolAst.module.fingerprint = 9167620621366789578 := by
  native_decide

theorem false_integer_equivalent : Bool.toInt Bool.false = 0 := by
  rfl

theorem true_integer_equivalent : Bool.toInt Bool.true = 1 := by
  rfl

end lang.py.builtin.type.bool
