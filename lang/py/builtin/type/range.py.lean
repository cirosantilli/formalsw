import «.cleanxy».lang.py.builtin.type.«range.py.ast»
import lang.py.builtin.type.range

namespace lang.py.builtin.type.range

open CleanXY.PyAst

theorem modeled :
    RangeAst.module.hasExactlyClassMethods "range"
      ["__init__", "__len__", "__contains__", "__getitem__"] = true := by
  rfl

theorem source_fingerprint : RangeAst.module.fingerprint = 18288300290557242368 := by
  native_decide

theorem positive_length_equivalent (start stop step : Int)
    (hstep : step > 0) (hnonempty : start < stop) :
    CleanXY.Py.Builtin.Range.length ⟨start, stop, step⟩ =
      ((stop - start - 1) / step + 1).toNat := by
  simp [CleanXY.Py.Builtin.Range.length, hstep, Int.not_le.mpr hnonempty]

end lang.py.builtin.type.range
