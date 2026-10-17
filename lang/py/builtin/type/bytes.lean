import lang.py.builtin.type.list
import lang.py.builtin.type.subsequence

/-! Python `bytes` semantics and the non-mutating portion shared with `bytearray`. -/

namespace FormalSW.Py.Builtin.Bytes

open FormalSW.Py.Builtin

abbrev ByteString := List UInt8

def empty : ByteString := []
def ofList (values : List UInt8) : ByteString := values
def zeros (size : Nat) : ByteString := List.replicate size 0
def size (values : ByteString) : Nat := values.length
def get? (values : ByteString) (index : Int) : Option UInt8 := Sequence.get? values index
def containsByte (values : ByteString) (value : UInt8) : Bool := values.contains value
def contains (values needle : ByteString) : Bool := Subsequence.contains values needle
def count (values needle : ByteString) : Nat := Subsequence.count values needle
def find? (values needle : ByteString) : Option Nat := Subsequence.find? values needle
def rfind? (values needle : ByteString) : Option Nat := Subsequence.rfind? values needle
def startsWith (values expected : ByteString) : Bool := Subsequence.startsWith values expected
def endsWith (values expected : ByteString) : Bool := Subsequence.endsWith values expected
def join (separator : ByteString) (values : List ByteString) : ByteString :=
  Subsequence.join separator values
def partition (values separator : ByteString) := Subsequence.partition values separator
def rpartition (values separator : ByteString) := Subsequence.rpartition values separator
def replace (values old replacement : ByteString) (count : Int := -1) : ByteString :=
  Subsequence.replace values old replacement count
def removePrefix (values prefixValue : ByteString) : ByteString :=
  Subsequence.removePrefix values prefixValue
def removeSuffix (values suffix : ByteString) : ByteString := Subsequence.removeSuffix values suffix
def split (values separator : ByteString) (maxSplit : Int := -1) :=
  Subsequence.split values separator maxSplit

def rsplit (values separator : ByteString) (maxSplit : Int := -1) : Result (List ByteString) := do
  let reversed ← Subsequence.split values.reverse separator.reverse maxSplit
  return reversed.map List.reverse |>.reverse

def index (values needle : ByteString) : Result Nat :=
  match find? values needle with
  | some position => .ok position
  | none => .error (.valueError "subsection not found")

def rindex (values needle : ByteString) : Result Nat :=
  match rfind? values needle with
  | some position => .ok position
  | none => .error (.valueError "subsection not found")

def isAsciiWhitespace (byte : UInt8) : Bool :=
  byte = 9 || byte = 10 || byte = 11 || byte = 12 || byte = 13 || byte = 32
def isAsciiDigit (byte : UInt8) : Bool := 48 ≤ byte.toNat && byte.toNat ≤ 57
def isAsciiUpper (byte : UInt8) : Bool := 65 ≤ byte.toNat && byte.toNat ≤ 90
def isAsciiLower (byte : UInt8) : Bool := 97 ≤ byte.toNat && byte.toNat ≤ 122
def isAsciiAlpha (byte : UInt8) : Bool := isAsciiUpper byte || isAsciiLower byte
def isAsciiAlnum (byte : UInt8) : Bool := isAsciiAlpha byte || isAsciiDigit byte

def toLowerByte (byte : UInt8) : UInt8 :=
  if isAsciiUpper byte then UInt8.ofNat (byte.toNat + 32) else byte
def toUpperByte (byte : UInt8) : UInt8 :=
  if isAsciiLower byte then UInt8.ofNat (byte.toNat - 32) else byte

def isAscii (values : ByteString) : Bool := values.all fun byte => byte.toNat < 128
def isAlpha (values : ByteString) : Bool := !values.isEmpty && values.all isAsciiAlpha
def isDigit (values : ByteString) : Bool := !values.isEmpty && values.all isAsciiDigit
def isAlnum (values : ByteString) : Bool := !values.isEmpty && values.all isAsciiAlnum
def isSpace (values : ByteString) : Bool := !values.isEmpty && values.all isAsciiWhitespace
def isLower (values : ByteString) : Bool :=
  values.any isAsciiLower && values.all fun byte => !isAsciiUpper byte
def isUpper (values : ByteString) : Bool :=
  values.any isAsciiUpper && values.all fun byte => !isAsciiLower byte

def lower (values : ByteString) : ByteString := values.map toLowerByte
def upper (values : ByteString) : ByteString := values.map toUpperByte
def swapCase (values : ByteString) : ByteString :=
  values.map fun byte =>
    if isAsciiLower byte then toUpperByte byte
    else if isAsciiUpper byte then toLowerByte byte
    else byte

def capitalize : ByteString → ByteString
  | [] => []
  | first :: rest => toUpperByte first :: rest.map toLowerByte

private def titleAux : Bool → ByteString → ByteString
  | _, [] => []
  | previousCased, byte :: rest =>
      let transformed := if previousCased then toLowerByte byte else toUpperByte byte
      transformed :: titleAux (isAsciiAlpha byte) rest

def title (values : ByteString) : ByteString := titleAux false values

private def isTitleAux : Bool → Bool → ByteString → Bool
  | _, sawCased, [] => sawCased
  | previousCased, sawCased, byte :: rest =>
      let valid :=
        if isAsciiUpper byte then !previousCased
        else if isAsciiLower byte then previousCased
        else true
      valid && isTitleAux (isAsciiAlpha byte) (sawCased || isAsciiAlpha byte) rest

def isTitle (values : ByteString) : Bool := isTitleAux false false values

private def dropWhile (predicate : UInt8 → Bool) : ByteString → ByteString
  | [] => []
  | head :: tail => if predicate head then dropWhile predicate tail else head :: tail

def lstrip (values : ByteString) (chars : Option ByteString := none) : ByteString :=
  let predicate := match chars with
    | none => isAsciiWhitespace
    | some chars => fun byte => chars.contains byte
  dropWhile predicate values

def rstrip (values : ByteString) (chars : Option ByteString := none) : ByteString :=
  (lstrip values.reverse chars).reverse

def strip (values : ByteString) (chars : Option ByteString := none) : ByteString :=
  rstrip (lstrip values chars) chars

def ljust (values : ByteString) (width : Int) (fill : UInt8 := 32) : ByteString :=
  values ++ List.replicate (width - values.length).toNat fill

def rjust (values : ByteString) (width : Int) (fill : UInt8 := 32) : ByteString :=
  List.replicate (width - values.length).toNat fill ++ values

def center (values : ByteString) (width : Int) (fill : UInt8 := 32) : ByteString :=
  let padding := (width - values.length).toNat
  let left := padding / 2
  List.replicate left fill ++ values ++ List.replicate (padding - left) fill

def zfill (values : ByteString) (width : Int) : ByteString :=
  let padding := List.replicate (width - values.length).toNat 48
  match values with
  | sign :: rest => if sign = 43 || sign = 45 then sign :: padding ++ rest else padding ++ values
  | [] => padding

private def expandTabsAux : Nat → Nat → ByteString → ByteString
  | _, _, [] => []
  | column, tabSize, byte :: rest =>
      if byte = 9 then
        let spaces := if tabSize = 0 then 0 else tabSize - column % tabSize
        List.replicate spaces 32 ++ expandTabsAux (column + spaces) tabSize rest
      else if byte = 10 || byte = 13 then byte :: expandTabsAux 0 tabSize rest
      else byte :: expandTabsAux (column + 1) tabSize rest

def expandTabs (values : ByteString) (tabSize : Int := 8) : ByteString :=
  expandTabsAux 0 tabSize.toNat values

private def splitLinesFuel : Nat → Bool → ByteString → List ByteString
  | 0, _, values => if values.isEmpty then [] else [values]
  | fuel + 1, keepEnds, values =>
      let position := (List.range (values.length + 1)).find? fun i =>
        match values.drop i with | 10 :: _ | 13 :: _ => true | _ => false
      match position with
      | none => if values.isEmpty then [] else [values]
      | some index =>
          let rest := values.drop index
          let breakLength := match rest with | 13 :: 10 :: _ => 2 | _ => 1
          let lineLength := if keepEnds then index + breakLength else index
          values.take lineLength :: splitLinesFuel fuel keepEnds (values.drop (index + breakLength))

def splitLines (values : ByteString) (keepEnds : Bool := false) : List ByteString :=
  splitLinesFuel (values.length + 1) keepEnds values

def makeTrans (fromBytes toBytes : ByteString) : Result ByteString :=
  if fromBytes.length != toBytes.length then
    .error (.valueError "maketrans arguments must have same length")
  else
    let replacements := (List.range 256).map UInt8.ofNat
    .ok <| (fromBytes.zip toBytes).foldl (fun table pair =>
      table.set pair.1.toNat pair.2) replacements

def maketrans (fromBytes toBytes : ByteString) : Result ByteString := makeTrans fromBytes toBytes

def translate (values table : ByteString) (delete : ByteString := []) : Result ByteString :=
  if table.length != 256 then .error (.valueError "translation table must be 256 characters long")
  else
    .ok <| values.filterMap fun byte =>
      if delete.contains byte then none else table[byte.toNat]?

private def hexDigit (value : Nat) : Char :=
  Char.ofNat (if value < 10 then 48 + value else 87 + value)

def hex (values : ByteString) : String :=
  String.ofList <| values.flatMap fun byte =>
    [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)]

/-- Python's printable bytes representation, including its quote choice. -/
def repr (values : ByteString) : String :=
  let quote := if values.contains 39 && !values.contains 34 then '"' else '\''
  let escaped := values.flatMap fun byte =>
    let n := byte.toNat
    if n = quote.toNat || n = 92 then ['\\', Char.ofNat n]
    else if n = 9 then ['\\', 't']
    else if n = 10 then ['\\', 'n']
    else if n = 13 then ['\\', 'r']
    else if 32 ≤ n && n < 127 then [Char.ofNat n]
    else ['\\', 'x', hexDigit (n / 16), hexDigit (n % 16)]
  String.ofList (['b', quote] ++ escaped ++ [quote])

private def hexValue (char : Char) : Option Nat :=
  let value := char.toNat
  if 48 ≤ value && value ≤ 57 then some (value - 48)
  else if 65 ≤ value && value ≤ 70 then some (value - 55)
  else if 97 ≤ value && value ≤ 102 then some (value - 87)
  else none

private def isHexWhitespace (char : Char) : Bool :=
  char = ' ' || char = '\t' || char = '\n' || char = '\r' || char = '\x0b' || char = '\x0c'

private def parseHex : List Char → Option Nat → Result ByteString
  | [], none => .ok []
  | [], some _ => .error (.valueError "non-hexadecimal number found in fromhex()")
  | char :: rest, high =>
      if isHexWhitespace char then parseHex rest high
      else
        match hexValue char, high with
        | none, _ => .error (.valueError "non-hexadecimal number found in fromhex()")
        | some nibble, none => parseHex rest (some nibble)
        | some nibble, some first =>
            (UInt8.ofNat (16 * first + nibble) :: ·) <$> parseHex rest none

def fromHex (source : String) : Result ByteString := parseHex source.toList none

/-- A named codec abstracts CPython's codec registry while retaining encode/decode failures. -/
structure Codec where
  encode : List Nat → Result ByteString
  decode : ByteString → Result (List Nat)

def decode (codec : Codec) (values : ByteString) : Result (List Nat) := codec.decode values

def fromString (codec : Codec) (value : List Nat) : Result ByteString := codec.encode value

structure PercentFormatter (α : Type u) where
  format : ByteString → α → Result ByteString

def percentFormat (formatter : PercentFormatter α) (template : ByteString)
    (arguments : α) : Result ByteString := formatter.format template arguments

example : hex [0, 15, 255] = "000fff" := rfl
example : fromHex "00 0f FF" = .ok [0, 15, 255] := rfl
example : capitalize [104, 69, 76, 76, 79] = [72, 101, 108, 108, 111] := rfl

end FormalSW.Py.Builtin.Bytes
