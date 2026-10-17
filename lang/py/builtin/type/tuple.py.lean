import «.formalsw».lang.py.builtin.type.«tuple.py.ast»
import lang.py.builtin.type.tuple

namespace lang.py.builtin.type.tuple

open FormalSW.PyAst

/-- The checked Python source is the list-backed tuple implementation used by the Lean model. -/
theorem modeled :
    TupleAst.module.hasExactlyClassMethods "tuple"
      ["__init__", "__eq__", "__lt__", "__le__", "__gt__", "__ge__", "__len__", "__getitem__"] = true := by
  rfl

theorem source_fingerprint : TupleAst.module.fingerprint = 4542874346801578048 := by
  native_decide

theorem length_equivalent (value : FormalSW.Py.Builtin.Tuple.Tuple α) :
    FormalSW.Py.Builtin.Tuple.size value = value.length := by
  rfl

end lang.py.builtin.type.tuple
