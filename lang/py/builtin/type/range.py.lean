import «.formalsw».lang.py.builtin.type.«range.py.ast»
import lang.py.builtin.type.range

namespace lang.py.builtin.type.range

open FormalSW.PyAst

theorem modeled :
    RangeAst.module.hasExactlyClassMethods "range"
      ["__init__", "__len__", "__contains__", "__getitem__"] = true := by
  rfl

theorem source_fingerprint : RangeAst.module.fingerprint = 14079189947378742754 := by
  native_decide

theorem positive_length_equivalent (start stop step : Int)
    (hstep : step > 0) (hnonempty : start < stop) :
    FormalSW.Py.Builtin.Range.length ⟨start, stop, step⟩ =
      ((stop - start - 1) / step + 1).toNat := by
  simp [FormalSW.Py.Builtin.Range.length, hstep, Int.not_le.mpr hnonempty]

end lang.py.builtin.type.range
