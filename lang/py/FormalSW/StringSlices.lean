import lang.py.FormalSW.Strings

/-! Negative-start reverse slices count characters or bytes, as appropriate. -/
namespace FormalSW.PyAst.Strings

/-- A negative start omits the final `skip` characters before reversing. -/
theorem slice_reverse_skip (text : String) (skip : Nat) :
    slice (.string text) (.int (-((skip : Int) + 1))) .none (.int (-1)) =
      .ok (.string (String.ofList (text.toList.take (text.toList.length - skip)).reverse)) := by
  change (match Py.Builtin.Sequence.slice text.toList
      { start := some (-((skip : Int) + 1)), step := some (-1) } with
    | .ok characters => Except.ok (Constant.string (String.ofList characters))
    | .error _ => Except.error ({ typeName := "ValueError", args := [] } : ExceptionObject)) = _
  rw [Py.Builtin.Sequence.slice_reverse_skip]

/-- Byte strings use the same bounds on their octets. -/
theorem slice_reverse_skip_bytes (bytes : List UInt8) (skip : Nat) :
    slice (.bytes bytes) (.int (-((skip : Int) + 1))) .none (.int (-1)) =
      .ok (.bytes (bytes.take (bytes.length - skip)).reverse) := by
  change (match Py.Builtin.Sequence.slice bytes
      { start := some (-((skip : Int) + 1)), step := some (-1) } with
    | .ok values => Except.ok (Constant.bytes values)
    | .error _ => Except.error ({ typeName := "ValueError", args := [] } : ExceptionObject)) = _
  rw [Py.Builtin.Sequence.slice_reverse_skip]

end FormalSW.PyAst.Strings
