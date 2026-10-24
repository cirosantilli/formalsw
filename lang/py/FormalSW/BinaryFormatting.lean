import lang.py.FormalSW.Strings

/-! Character-list interface for Python's signed binary formatter. -/
namespace FormalSW.PyAst.Strings

/-- Nonnegative integers include the usual prefix and all binary digits, including zero. -/
theorem binaryRepresentation_nat (value : Nat) :
    (binaryRepresentation (value : Int)).toList = ['0', 'b'] ++ Nat.toDigits 2 value := by
  simp [binaryRepresentation, Py.Builtin.Function.Conversion.bin_nat, List.map_map, Function.comp_def]

end FormalSW.PyAst.Strings
