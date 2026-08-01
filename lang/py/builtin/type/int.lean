import lang.py.builtin.type.core

/-! Arbitrary-precision Python integer operations, excluding float-producing branches. -/

namespace CleanXY.Py.Builtin.Int

open CleanXY.Py.Builtin

/-- Python integers have arbitrary precision, directly represented by Lean integers. -/
abbrev IntValue := Int

inductive ByteOrder where
  | big
  | little
deriving Repr, DecidableEq

def abs (value : IntValue) : IntValue := Int.natAbs value
def add (left right : IntValue) : IntValue := left + right
def sub (left right : IntValue) : IntValue := left - right
def mul (left right : IntValue) : IntValue := left * right
def neg (value : IntValue) : IntValue := -value
def pos (value : IntValue) : IntValue := value
def truth (value : IntValue) : Bool := value != 0
def equal (left right : IntValue) : Bool := left = right
def lessThan (left right : IntValue) : Bool := left < right
def lessEqual (left right : IntValue) : Bool := left ≤ right
def greaterThan (left right : IntValue) : Bool := left > right
def greaterEqual (left right : IntValue) : Bool := left ≥ right

/-- Python `//`, which rounds toward negative infinity. -/
def floorDiv (left right : IntValue) : Result IntValue :=
  if right = 0 then
    .error (.zeroDivisionError "integer division or modulo by zero")
  else
    .ok (Int.fdiv left right)

/-- Python `%`; its result has the divisor's sign and satisfies `a = b*q + r`. -/
def mod (left right : IntValue) : Result IntValue := do
  let quotient ← floorDiv left right
  return left - right * quotient

def divMod (left right : IntValue) : Result (IntValue × IntValue) := do
  let quotient ← floorDiv left right
  return (quotient, left - right * quotient)

def pow (base exponent : IntValue) : Result IntValue :=
  if exponent < 0 then
    .error (.floatingPointExcluded "pow with a negative exponent and no modulus")
  else
    .ok (_root_.Int.pow base exponent.toNat)

private def rawMod (left right : Int) : Int := left - right * Int.fdiv left right

private def powModNat (base : Int) : Nat → Int → Int
  | 0, modulus => rawMod 1 modulus
  | exponent + 1, modulus =>
      rawMod (base * powModNat base exponent modulus) modulus

private def inverseSearch : Nat → Nat → Int → Int → Option Int
  | 0, _, _, _ => none
  | fuel + 1, candidate, value, modulus =>
      if Int.emod (value * candidate) modulus.natAbs = 1 then some candidate
      else inverseSearch fuel (candidate + 1) value modulus

/-- Multiplicative inverse modulo `modulus`, when one exists. -/
def modularInverse? (value modulus : IntValue) : Option IntValue :=
  if modulus.natAbs ≤ 1 then none
  else
    match inverseSearch modulus.natAbs 0 value modulus with
    | none => none
    | some inverse => some (rawMod inverse modulus)

/-- Three-argument `pow` for non-negative integer exponents. -/
def powMod (base exponent modulus : IntValue) : Result IntValue :=
  if modulus = 0 then
    .error (.valueError "pow() 3rd argument cannot be 0")
  else if exponent < 0 then
    match modularInverse? base modulus with
    | none => .error (.valueError "base is not invertible for the given modulus")
    | some inverse => .ok (powModNat inverse (-exponent).toNat modulus)
  else .ok (powModNat base exponent.toNat modulus)

def bitAnd : IntValue → IntValue → IntValue
  | .ofNat left, .ofNat right => .ofNat (left &&& right)
  | .ofNat left, .negSucc right => .ofNat (left ^^^ (left &&& right))
  | .negSucc left, .ofNat right => .ofNat (right ^^^ (right &&& left))
  | .negSucc left, .negSucc right => .negSucc (left ||| right)

def bitOr : IntValue → IntValue → IntValue
  | .ofNat left, .ofNat right => .ofNat (left ||| right)
  | .ofNat left, .negSucc right => .negSucc (right ^^^ (right &&& left))
  | .negSucc left, .ofNat right => .negSucc (left ^^^ (left &&& right))
  | .negSucc left, .negSucc right => .negSucc (left &&& right)

def bitXor : IntValue → IntValue → IntValue
  | .ofNat left, .ofNat right => .ofNat (left ^^^ right)
  | .ofNat left, .negSucc right => .negSucc (left ^^^ right)
  | .negSucc left, .ofNat right => .negSucc (left ^^^ right)
  | .negSucc left, .negSucc right => .ofNat (left ^^^ right)
def bitNot (value : IntValue) : IntValue := ~~~value

def shiftLeft (value count : IntValue) : Result IntValue :=
  if count < 0 then .error (.valueError "negative shift count")
  else .ok (_root_.Int.shiftLeft value count.toNat)

def shiftRight (value count : IntValue) : Result IntValue :=
  if count < 0 then .error (.valueError "negative shift count")
  else .ok (_root_.Int.shiftRight value count.toNat)

/-- Number of bits needed for the absolute value, excluding sign and leading zeros. -/
def bitLength (value : IntValue) : Nat :=
  let magnitude := value.natAbs
  if magnitude = 0 then 0 else Nat.log2 magnitude + 1

private def bitCountFuel : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, value => value % 2 + bitCountFuel fuel (value / 2)

/-- Number of ones in the binary representation of the absolute value. -/
def bitCount (value : IntValue) : Nat :=
  let magnitude := value.natAbs
  bitCountFuel (bitLength value) magnitude

private def bytesLittleEndian : Nat → Nat → List UInt8
  | 0, _ => []
  | length + 1, value =>
      UInt8.ofNat (value % 256) :: bytesLittleEndian length (value / 256)

private def unsignedBounds (length : Nat) : Int × Int :=
  (0, (256 : Int) ^ length)

private def signedBounds (length : Nat) : Int × Int :=
  if length = 0 then (0, 1)
  else
    let half := (2 : Int) ^ (8 * length - 1)
    (-half, half)

/-- Python `int.to_bytes`, including signed two's-complement encoding. -/
def toBytes (value : IntValue) (length : Nat) (byteOrder : ByteOrder := .big)
    (signed : Bool := false) : Result (List UInt8) :=
  let bounds := if signed then signedBounds length else unsignedBounds length
  if value < bounds.1 || value ≥ bounds.2 then
    .error (.overflowError "int too big to convert")
  else
    let modulus := (256 : Int) ^ length
    let encoded := (Int.emod value modulus).toNat
    let little := bytesLittleEndian length encoded
    .ok (if byteOrder = .little then little else little.reverse)

private def unsignedFromLittleEndian : List UInt8 → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * unsignedFromLittleEndian rest

/-- Python `int.from_bytes`, including signed two's-complement decoding. -/
def fromBytes (bytes : List UInt8) (byteOrder : ByteOrder := .big)
    (signed : Bool := false) : IntValue :=
  let little := if byteOrder = .little then bytes else bytes.reverse
  let unsigned : Int := unsignedFromLittleEndian little
  if signed && (little.getLast?.any fun byte => byte.toNat ≥ 128) then
    unsigned - (256 : Int) ^ bytes.length
  else
    unsigned

def asIntegerRatio (value : IntValue) : IntValue × IntValue := (value, 1)
def isInteger (_ : IntValue) : Bool := true

private def isAsciiSpace (codePoint : Nat) : Bool :=
  codePoint = 9 || codePoint = 10 || codePoint = 11 || codePoint = 12 ||
    codePoint = 13 || codePoint = 32

private def trimLeft : List Nat → List Nat
  | [] => []
  | head :: tail => if isAsciiSpace head then trimLeft tail else head :: tail

private def trim (value : List Nat) : List Nat := (trimLeft value.reverse).reverse |> trimLeft

private def digitValue (codePoint : Nat) : Option Nat :=
  if 48 ≤ codePoint && codePoint ≤ 57 then some (codePoint - 48)
  else if 65 ≤ codePoint && codePoint ≤ 90 then some (codePoint - 55)
  else if 97 ≤ codePoint && codePoint ≤ 122 then some (codePoint - 87)
  else none

private def inferBase (requested : Nat) : List Nat → Nat × List Nat
  | 48 :: marker :: rest =>
      if marker = 98 || marker = 66 then (if requested = 0 then 2 else requested, rest)
      else if marker = 111 || marker = 79 then (if requested = 0 then 8 else requested, rest)
      else if marker = 120 || marker = 88 then (if requested = 0 then 16 else requested, rest)
      else (if requested = 0 then 10 else requested, 48 :: marker :: rest)
  | digits => (if requested = 0 then 10 else requested, digits)

private def parseDigits (base : Nat) : List Nat → Bool → Bool → Result Nat
  | [], sawDigit, previousUnderscore =>
      if sawDigit && !previousUnderscore then .ok 0
      else .error (.valueError "invalid literal for int()")
  | codePoint :: rest, sawDigit, previousUnderscore =>
      if codePoint = 95 then
        if !sawDigit || previousUnderscore then .error (.valueError "invalid literal for int()")
        else parseDigits base rest sawDigit true
      else
        match digitValue codePoint with
        | none => .error (.valueError "invalid literal for int()")
        | some digit =>
            if digit ≥ base then .error (.valueError "invalid literal for int()")
            else do
              let suffix ← parseDigits base rest true false
              return digit * base ^ (rest.filter (· != 95)).length + suffix

/-- `int(string, base)`, for bases zero or 2 through 36. -/
def parse (source : List Nat) (requestedBase : Nat := 10) : Result IntValue :=
  if requestedBase != 0 && (requestedBase < 2 || requestedBase > 36) then
    .error (.valueError "int() base must be >= 2 and <= 36, or 0")
  else
    let stripped := trim source
    let (negative, unsigned) := match stripped with
      | 43 :: rest => (false, rest)
      | 45 :: rest => (true, rest)
      | rest => (false, rest)
    let (base, digits) := inferBase requestedBase unsigned
    if requestedBase != 0 && base != requestedBase then
      .error (.valueError "invalid literal for int()")
    else do
      let magnitude ← parseDigits base digits false false
      return if negative then -(magnitude : Int) else magnitude

example : floorDiv (-3) 2 = .ok (-2) := rfl
example : mod 3 (-2) = .ok (-1) := rfl
example : bitLength 0 = 0 := rfl
example : bitLength 255 = 8 := rfl
example : bitCount 13 = 3 := rfl
example : toBytes 1024 2 = .ok [4, 0] := rfl
example : fromBytes [255] .big true = -1 := rfl
example : powMod 3 (-1) 11 = .ok 4 := rfl
example : powMod 2 (-1) 4 = .error (.valueError "base is not invertible for the given modulus") := rfl
example : parse [45, 48, 120, 102, 102] 0 = .ok (-255) := rfl
example : parse [49, 95, 48, 48, 48] = .ok 1000 := rfl

end CleanXY.Py.Builtin.Int
