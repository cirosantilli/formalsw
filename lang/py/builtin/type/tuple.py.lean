import «.cleanxy».lang.py.builtin.type.«tuple.py.ast»
import lang.py.builtin.type.tuple

namespace lang.py.builtin.type.tuple

open CleanXY.PyAst

/-- The checked Python source is the list-backed tuple implementation used by the Lean model. -/
theorem modeled :
    TupleAst.module.hasExactlyClassMethods "tuple"
      ["__init__", "__eq__", "__lt__", "__le__", "__gt__", "__ge__", "__len__", "__getitem__"] = true := by
  rfl

theorem source_fingerprint : TupleAst.module.fingerprint = 13455955072439172151 := by
  native_decide

theorem length_equivalent (value : CleanXY.Py.Builtin.Tuple.Tuple α) :
    CleanXY.Py.Builtin.Tuple.size value = value.length := by
  rfl

end lang.py.builtin.type.tuple
