import lang.py.builtin.type.core

/-! Unicode 16.0 numeric properties used by Python 3.14.
Decimal blocks come from https://www.unicode.org/Public/16.0.0/ucd/UnicodeData.txt.
Each entry starts a consecutive block of ten decimal digits. -/
namespace FormalSW.Py.Builtin.Unicode

def decimalZeroes : List Nat := [
  0x30, 0x660, 0x6f0, 0x7c0, 0x966, 0x9e6, 0xa66, 0xae6,
  0xb66, 0xbe6, 0xc66, 0xce6, 0xd66, 0xde6, 0xe50, 0xed0,
  0xf20, 0x1040, 0x1090, 0x17e0, 0x1810, 0x1946, 0x19d0,
  0x1a80, 0x1a90, 0x1b50, 0x1bb0, 0x1c40, 0x1c50, 0xa620,
  0xa8d0, 0xa900, 0xa9d0, 0xa9f0, 0xaa50, 0xabf0, 0xff10,
  0x104a0, 0x10d30, 0x10d40, 0x11066, 0x110f0, 0x11136,
  0x111d0, 0x112f0, 0x11450, 0x114d0, 0x11650, 0x116c0,
  0x116d0, 0x116da, 0x11730, 0x118e0, 0x11950, 0x11bf0,
  0x11c50, 0x11d50, 0x11da0, 0x11f50, 0x16130, 0x16a60,
  0x16ac0, 0x16b50, 0x16d70, 0x1ccf0, 0x1d7ce, 0x1d7d8,
  0x1d7e2, 0x1d7ec, 0x1d7f6, 0x1e140, 0x1e2f0, 0x1e4f0,
  0x1e5f1, 0x1e950, 0x1fbf0]

def decimalValue? (codePoint : Nat) : Option Nat :=
  (decimalZeroes.find? fun first => first ≤ codePoint && codePoint < first + 10).map (codePoint - ·)

/-- Numeric_Type=Digit, excluding the separate Decimal property.
Ranges are inclusive, from Unicode 16.0 extracted/DerivedNumericType.txt. -/
def digitRanges : List (Nat × Nat) := [
  (0xb2, 0xb3), (0xb9, 0xb9), (0x1369, 0x1371), (0x19da, 0x19da),
  (0x2070, 0x2070), (0x2074, 0x2079), (0x2080, 0x2089), (0x2460, 0x2468),
  (0x2474, 0x247c), (0x2488, 0x2490), (0x24ea, 0x24ea), (0x24f5, 0x24fd),
  (0x24ff, 0x24ff), (0x2776, 0x277e), (0x2780, 0x2788), (0x278a, 0x2792),
  (0x10a40, 0x10a43), (0x10e60, 0x10e68), (0x11052, 0x1105a), (0x1f100, 0x1f10a)]

/-- Python includes both Numeric_Type=Decimal and Numeric_Type=Digit. -/
def isDigit (codePoint : Nat) : Bool :=
  (decimalValue? codePoint).isSome ||
    digitRanges.any fun (first, last) => first ≤ codePoint && codePoint ≤ last

/-- Non-ASCII whitespace is normalized by Python's Unicode-to-integer conversion.
ASCII control separators U+001C–U+001F are deliberately not normalized. -/
def integerSpace (codePoint : Nat) : Bool :=
  codePoint = 0x85 || codePoint = 0xa0 || codePoint = 0x1680 ||
    (0x2000 ≤ codePoint && codePoint ≤ 0x200a) || codePoint = 0x2028 ||
    codePoint = 0x2029 || codePoint = 0x202f || codePoint = 0x205f || codePoint = 0x3000

/-- Preserve ASCII syntax; normalize Unicode decimal digits and whitespace.
Other characters map to an invalid integer-literal character. -/
def integerCharacter (character : Char) : Nat :=
  let point := character.toNat
  if point < 128 then point
  else if integerSpace point then 32
  else match decimalValue? point with
    | some digit => 48 + digit
    | none => 256

end FormalSW.Py.Builtin.Unicode
