import lang.py.FormalSW.Runtime
import lang.py.builtin.type.sequence
import lang.py.builtin.type.bytes
import lang.py.builtin.function

/-! Scalar sequence operations distinguish Unicode characters from raw bytes.
As with the unbounded call stack, decimal conversion has no configurable
resource limit (CPython's `PYTHONINTMAXSTRDIGITS=0` configuration). -/

namespace FormalSW.PyAst.Strings

/-- Unicode whitespace recognized by Python's string methods, including the C0 separators. -/
def whitespaceCodepoints : List Nat :=
  [0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x1c, 0x1d, 0x1e, 0x1f, 0x20,
    0x85, 0xa0, 0x1680, 0x2000, 0x2001, 0x2002, 0x2003, 0x2004, 0x2005,
    0x2006, 0x2007, 0x2008, 0x2009, 0x200a, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000]

def isWhitespace (character : Char) : Bool := whitespaceCodepoints.contains character.toNat

/-- Zero-argument strip removes whitespace at both ends while retaining internal characters. -/
def stripWhitespace (text : String) : String :=
  String.ofList (((text.toList.dropWhile isWhitespace).reverse.dropWhile isWhitespace).reverse)

/-- Zero-argument split coalesces whitespace and omits empty boundary fields. -/
def splitWhitespace (text : String) : List String :=
  ((text.toList.splitOnP isWhitespace).filter (fun word => !word.isEmpty)).map String.ofList

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

/-- Zero padding counts Unicode characters and follows an optional ASCII sign. -/
def zfill (text : String) (width : Int) : String :=
  let padding := List.replicate (width-text.toList.length).toNat '0'
  String.ofList (match text.toList with
    | sign::rest => if sign='+' ∨ sign='-' then sign::padding++rest else padding++text.toList
    | [] => padding)

def zfillCall (text : String) : List Constant → Except ExceptionObject Constant
  | [width] => match scalarNumber width with
      | some width => .ok (.string (zfill text width))
      | none => .error typeError
  | _ => .error typeError

/-- Binary formatting uses the shared signed, arbitrary-precision builtin model. -/
def binaryRepresentation (value : Int) : String :=
  String.ofList ((Py.Builtin.Function.Conversion.bin value).map Char.ofNat)

def bin : List Constant → Except ExceptionObject Constant
  | [value] => match scalarNumber value with
      | some number => .ok (.string (binaryRepresentation number))
      | none => .error typeError
  | _ => .error typeError

/-- Unicode substring membership, including the empty substring. -/
def contains (text substring : String) : Bool :=
  Py.Builtin.Subsequence.contains text.toList substring.toList

theorem contains_eq_isInfix (text substring : String) :
    contains text substring = substring.toList.isInfixOf_internal text.toList :=
  Py.Builtin.Subsequence.contains_eq_isInfix _ _

/-- A Unicode character or a single byte has an ordinal; other lengths and types fail. -/
def ord : Constant → Except ExceptionObject Constant
  | .string text => match text.toList with
      | [character] => .ok (.int character.toNat)
      | _ => .error typeError
  | .bytes [byte] => .ok (.int byte.toNat)
  | _ => .error typeError

@[simp] theorem ord_character (character : Char) :
    ord (.string (String.ofList [character])) = .ok (.int character.toNat) := by
  simp [ord]

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
