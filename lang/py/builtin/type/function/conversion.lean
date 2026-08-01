import lang.py.builtin.type.bool
import lang.py.builtin.type.int
import lang.py.builtin.type.str

/-! Pure conversion builtins, excluding constructors whose target is floating point. -/

namespace CleanXY.Py.Builtin.Function.Conversion

open CleanXY.Py.Builtin

private def digit (value : Nat) : Nat := if value < 10 then 48 + value else 87 + value

private def digitsFuel (base : Nat) : Nat → Nat → Str.Str
  | 0, _ => []
  | fuel + 1, value =>
      if value < base then [digit value]
      else digitsFuel base fuel (value / base) ++ [digit (value % base)]

private def formatUnsigned (base value : Nat) : Str.Str :=
  if value = 0 then [48] else digitsFuel base (value + 1) value

private def formatInteger (base : Nat) (prefixValue : Str.Str) (value : Int) : Str.Str :=
  let sign := if value < 0 then [45] else []
  sign ++ prefixValue ++ formatUnsigned base value.natAbs

def bin (value : Int) : Str.Str := formatInteger 2 [48, 98] value
def oct (value : Int) : Str.Str := formatInteger 8 [48, 111] value
def hex (value : Int) : Str.Str := formatInteger 16 [48, 120] value
def chr (value : Int) : Result Str.Str := Str.chr value
def ord (value : Str.Str) : Result Int := Str.ord value

def bool (truth : α → Bool) (object : α) : Bool := truth object
def intOfBool (value : Bool) : Int := Bool.toInt value

/-- Object-specific representation and formatting hooks used by `repr`, `ascii`, and `format`. -/
structure Representation (α : Type u) where
  repr : α → Result Str.Str
  str : α → Result Str.Str
  format : α → Str.Str → Result Str.Str

def repr (representation : Representation α) (object : α) : Result Str.Str :=
  representation.repr object

private def hexFixed (width value : Nat) : Str.Str :=
  let raw := formatUnsigned 16 value
  List.replicate (width - raw.length) 48 ++ raw

private def escapeCodePoint (value : Nat) : Str.Str :=
  if value < 128 then [value]
  else if value < 256 then [92, 120] ++ hexFixed 2 value
  else if value ≤ 0xffff then [92, 117] ++ hexFixed 4 value
  else [92, 85] ++ hexFixed 8 value

def ascii (representation : Representation α) (object : α) : Result Str.Str := do
  let rendered ← representation.repr object
  return rendered.flatMap escapeCodePoint

def format (representation : Representation α) (object : α) (specification : Str.Str := []) :=
  representation.format object specification

example : bin (-10) = [45, 48, 98, 49, 48, 49, 48] := rfl
example : hex 255 = [48, 120, 102, 102] := rfl

end CleanXY.Py.Builtin.Function.Conversion
