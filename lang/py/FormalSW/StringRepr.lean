import lang.py.FormalSW.Strings
import lang.py.builtin.type.unicode_printable

/-! Python scalar representations, including Unicode escaping and quote selection. -/
namespace FormalSW.PyAst.Strings

private def hexDigit (value : Nat) : Char :=
  Char.ofNat (if value < 10 then 48 + value else 87 + value)

/-- Escape widths are the two, four or eight hexadecimal places prescribed by Python. -/
def reprHex (width value : Nat) : List Char :=
  (List.range width).reverse.map fun offset => hexDigit (value / 16 ^ offset % 16)

def reprCharacter (quote codePoint : Nat) : List Char :=
  if codePoint = quote || codePoint = 92 then ['\\', Char.ofNat codePoint]
  else if codePoint = 9 then ['\\', 't']
  else if codePoint = 10 then ['\\', 'n']
  else if codePoint = 13 then ['\\', 'r']
  else if Py.Builtin.Unicode.isPrintable codePoint then [Char.ofNat codePoint]
  else if codePoint < 0x100 then ['\\', 'x'] ++ reprHex 2 codePoint
  else if codePoint < 0x10000 then ['\\', 'u'] ++ reprHex 4 codePoint
  else ['\\', 'U'] ++ reprHex 8 codePoint

/-- Code points also allow escaping isolated surrogates without constructing a Lean Char. -/
def reprCodePoints (points : List Nat) : String :=
  let quote := if points.contains 39 && !points.contains 34 then 34 else 39
  String.ofList ([Char.ofNat quote] ++ points.flatMap (reprCharacter quote) ++ [Char.ofNat quote])

def reprText (text : String) : String := reprCodePoints (text.toList.map Char.toNat)

def reprValue : Constant → String
  | .string text => reprText text
  | value => convert value

def repr : List Constant → Except ExceptionObject Constant
  | [value] => .ok (.string (reprValue value))
  | _ => .error { typeName := "TypeError", args := [] }

end FormalSW.PyAst.Strings
