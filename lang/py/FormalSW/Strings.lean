import lang.py.FormalSW.Runtime
import lang.py.builtin.type.sequence
import lang.py.builtin.type.bytes

/-! Scalar sequence operations distinguish Unicode characters from raw bytes.
As with the unbounded call stack, decimal conversion has no configurable
resource limit (CPython's `PYTHONINTMAXSTRDIGITS=0` configuration). -/

namespace FormalSW.PyAst.Strings

private def typeError : ExceptionObject := { typeName := "TypeError", args := [] }
private def valueError : ExceptionObject := { typeName := "ValueError", args := [] }
private def indexError : ExceptionObject := { typeName := "IndexError", args := [] }

def convert : Constant → String
  | .int n => toString n
  | .bool true => "True"
  | .bool false => "False"
  | .string s => s
  | .bytes bytes => Py.Builtin.Bytes.repr bytes
  | .none => "None"

def str : List Constant → Except ExceptionObject Constant
  | [] => .ok (.string "")
  | [value] => .ok (.string (convert value))
  | _ => .error typeError

def get (value index : Constant) : Except ExceptionObject Constant :=
  match value, scalarNumber index with
  | .bytes bytes, some index =>
      match Py.Builtin.Sequence.get? bytes index with
      | some byte => .ok (.int byte.toNat)
      | none => .error indexError
  | .string text, some index =>
      match Py.Builtin.Sequence.get? text.toList index with
      | some character => .ok (.string (String.ofList [character]))
      | none => .error indexError
  | _, _ => .error typeError

private def bound : Constant → Except ExceptionObject (Option Int)
  | .none => .ok none
  | value => match scalarNumber value with
      | some n => .ok (some n)
      | none => .error typeError

/-- Bounds are evaluated before subscription. Conversion validates the step
first, then start and stop, as Python sequence subscription does. -/
def slice (value lower upper stride : Constant) : Except ExceptionObject Constant := do
  match value with
  | .bytes bytes =>
      let stride ← bound stride
      if stride = some 0 then throw valueError
      let lower ← bound lower
      let upper ← bound upper
      match Py.Builtin.Sequence.slice bytes ⟨lower, upper, stride⟩ with
      | .ok bytes => return .bytes bytes
      | .error _ => throw valueError
  | .string text =>
      let stride ← bound stride
      if stride = some 0 then throw valueError
      let lower ← bound lower
      let upper ← bound upper
      match Py.Builtin.Sequence.slice text.toList ⟨lower, upper, stride⟩ with
      | .ok characters => return .string (String.ofList characters)
      | .error _ => throw valueError
  | _ => throw typeError

theorem slice_reverse (text : String) :
    slice (.string text) .none .none (.int (-1)) =
      .ok (.string (String.ofList text.toList.reverse)) := by
  change (match Py.Builtin.Sequence.slice text.toList { step := some (-1) } with
    | .ok characters => Except.ok (Constant.string (String.ofList characters))
    | .error _ => Except.error valueError) = _
  rw [Py.Builtin.Sequence.slice_reverse]

theorem slice_reverse_bytes (bytes : List UInt8) :
    slice (.bytes bytes) .none .none (.int (-1)) = .ok (.bytes bytes.reverse) := by
  change (match Py.Builtin.Sequence.slice bytes { step := some (-1) } with
    | .ok values => Except.ok (Constant.bytes values)
    | .error _ => Except.error valueError) = _
  rw [Py.Builtin.Sequence.slice_reverse]

end FormalSW.PyAst.Strings
