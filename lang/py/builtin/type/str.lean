import lang.py.builtin.type.bytes
import lang.py.builtin.type.dict
import lang.py.builtin.type.subsequence

/-!
Python Unicode strings. Strings are sequences of scalar code points. Character
properties and mappings are supplied by a Unicode database, while all sequence
and method algorithms are modeled here.
-/

namespace CleanXY.Py.Builtin.Str

open CleanXY.Py.Builtin

abbrev CodePoint := Nat
abbrev Str := List CodePoint

/-- Versioned Unicode properties used by Python's text methods. -/
structure UnicodeData where
  isAlpha : CodePoint → Bool
  isDecimal : CodePoint → Bool
  isDigit : CodePoint → Bool
  isNumeric : CodePoint → Bool
  isLower : CodePoint → Bool
  isUpper : CodePoint → Bool
  isTitle : CodePoint → Bool
  isWhitespace : CodePoint → Bool
  isPrintable : CodePoint → Bool
  isXidStart : CodePoint → Bool
  isXidContinue : CodePoint → Bool
  lower : CodePoint → Str
  upper : CodePoint → Str
  title : CodePoint → Str
  casefold : CodePoint → Str

def isValidCodePoint (value : Nat) : Bool := value ≤ 0x10ffff

def chr (value : Int) : Result Str :=
  if value < 0 || value > 0x10ffff then
    .error (.valueError "chr() arg not in range(0x110000)")
  else .ok [value.toNat]

def ord (value : Str) : Result Int :=
  match value with
  | [codePoint] => .ok codePoint
  | _ => .error (.typeError "ord() expected a character")

def size (value : Str) : Nat := value.length
def get? (value : Str) (index : Int) : Option CodePoint := Sequence.get? value index
def contains (value substring : Str) : Bool := Subsequence.contains value substring
def count (value substring : Str) : Nat := Subsequence.count value substring
def find? (value substring : Str) : Option Nat := Subsequence.find? value substring
def rfind? (value substring : Str) : Option Nat := Subsequence.rfind? value substring
def startsWith (value expected : Str) : Bool := Subsequence.startsWith value expected
def endsWith (value expected : Str) : Bool := Subsequence.endsWith value expected
def join (separator : Str) (values : List Str) : Str := Subsequence.join separator values
def partition (value separator : Str) := Subsequence.partition value separator
def rpartition (value separator : Str) := Subsequence.rpartition value separator
def replace (value old replacement : Str) (count : Int := -1) : Str :=
  Subsequence.replace value old replacement count
def removePrefix (value prefixValue : Str) : Str := Subsequence.removePrefix value prefixValue
def removeSuffix (value suffix : Str) : Str := Subsequence.removeSuffix value suffix
def split (value separator : Str) (maxSplit : Int := -1) :=
  Subsequence.split value separator maxSplit

def rsplit (value separator : Str) (maxSplit : Int := -1) : Result (List Str) := do
  let reversed ← Subsequence.split value.reverse separator.reverse maxSplit
  return reversed.map List.reverse |>.reverse

def index (value substring : Str) : Result Nat :=
  match find? value substring with
  | some position => .ok position
  | none => .error (.valueError "substring not found")

def rindex (value substring : Str) : Result Nat :=
  match rfind? value substring with
  | some position => .ok position
  | none => .error (.valueError "substring not found")

def isAscii (value : Str) : Bool := value.all (· < 128)
def isAlpha (unicode : UnicodeData) (value : Str) : Bool :=
  !value.isEmpty && value.all unicode.isAlpha
def isDecimal (unicode : UnicodeData) (value : Str) : Bool :=
  !value.isEmpty && value.all unicode.isDecimal
def isDigit (unicode : UnicodeData) (value : Str) : Bool :=
  !value.isEmpty && value.all unicode.isDigit
def isNumeric (unicode : UnicodeData) (value : Str) : Bool :=
  !value.isEmpty && value.all unicode.isNumeric
def isAlnum (unicode : UnicodeData) (value : Str) : Bool :=
  !value.isEmpty && value.all fun c =>
    unicode.isAlpha c || unicode.isDecimal c || unicode.isDigit c || unicode.isNumeric c
def isSpace (unicode : UnicodeData) (value : Str) : Bool :=
  !value.isEmpty && value.all unicode.isWhitespace
def isPrintable (unicode : UnicodeData) (value : Str) : Bool := value.all unicode.isPrintable

def isCased (unicode : UnicodeData) (codePoint : CodePoint) : Bool :=
  unicode.isLower codePoint || unicode.isUpper codePoint || unicode.isTitle codePoint

def isLower (unicode : UnicodeData) (value : Str) : Bool :=
  value.any unicode.isLower && value.all fun c => !unicode.isUpper c && !unicode.isTitle c
def isUpper (unicode : UnicodeData) (value : Str) : Bool :=
  value.any unicode.isUpper && value.all fun c => !unicode.isLower c && !unicode.isTitle c

def isIdentifier (unicode : UnicodeData) : Str → Bool
  | [] => false
  | first :: rest =>
      (unicode.isXidStart first || first = 95) &&
        rest.all fun c => unicode.isXidContinue c || c = 95

def lower (unicode : UnicodeData) (value : Str) : Str := value.flatMap unicode.lower
def upper (unicode : UnicodeData) (value : Str) : Str := value.flatMap unicode.upper
def casefold (unicode : UnicodeData) (value : Str) : Str := value.flatMap unicode.casefold

def capitalize (unicode : UnicodeData) : Str → Str
  | [] => []
  | first :: rest => unicode.title first ++ rest.flatMap unicode.lower

def swapCase (unicode : UnicodeData) (value : Str) : Str :=
  value.flatMap fun c =>
    if unicode.isUpper c then unicode.lower c
    else if unicode.isLower c then unicode.upper c
    else c :: []

private def titleAux (unicode : UnicodeData) : Bool → Str → Str
  | _, [] => []
  | previousCased, codePoint :: rest =>
      let mapped := if previousCased then unicode.lower codePoint else unicode.title codePoint
      mapped ++ titleAux unicode (isCased unicode codePoint) rest

def title (unicode : UnicodeData) (value : Str) : Str := titleAux unicode false value

private def isTitleAux (unicode : UnicodeData) : Bool → Bool → Str → Bool
  | _, sawCased, [] => sawCased
  | previousCased, sawCased, codePoint :: rest =>
      let valid :=
        if unicode.isUpper codePoint || unicode.isTitle codePoint then !previousCased
        else if unicode.isLower codePoint then previousCased
        else true
      valid && isTitleAux unicode (isCased unicode codePoint)
        (sawCased || isCased unicode codePoint) rest

def isTitle (unicode : UnicodeData) (value : Str) : Bool :=
  isTitleAux unicode false false value

private def dropWhile (predicate : CodePoint → Bool) : Str → Str
  | [] => []
  | head :: tail => if predicate head then dropWhile predicate tail else head :: tail

def lstrip (unicode : UnicodeData) (value : Str) (chars : Option Str := none) : Str :=
  let predicate := match chars with
    | none => unicode.isWhitespace
    | some chars => fun codePoint => chars.contains codePoint
  dropWhile predicate value

def rstrip (unicode : UnicodeData) (value : Str) (chars : Option Str := none) : Str :=
  (lstrip unicode value.reverse chars).reverse

def strip (unicode : UnicodeData) (value : Str) (chars : Option Str := none) : Str :=
  rstrip unicode (lstrip unicode value chars) chars

def ljust (value : Str) (width : Int) (fill : CodePoint := 32) : Str :=
  value ++ List.replicate (width - value.length).toNat fill
def rjust (value : Str) (width : Int) (fill : CodePoint := 32) : Str :=
  List.replicate (width - value.length).toNat fill ++ value
def center (value : Str) (width : Int) (fill : CodePoint := 32) : Str :=
  let padding := (width - value.length).toNat
  let left := padding / 2
  List.replicate left fill ++ value ++ List.replicate (padding - left) fill

def zfill (value : Str) (width : Int) : Str :=
  let padding := List.replicate (width - value.length).toNat 48
  match value with
  | sign :: rest => if sign = 43 || sign = 45 then sign :: padding ++ rest else padding ++ value
  | [] => padding

private def expandTabsAux : Nat → Nat → Str → Str
  | _, _, [] => []
  | column, tabSize, codePoint :: rest =>
      if codePoint = 9 then
        let spaces := if tabSize = 0 then 0 else tabSize - column % tabSize
        List.replicate spaces 32 ++ expandTabsAux (column + spaces) tabSize rest
      else if codePoint = 10 || codePoint = 13 then
        codePoint :: expandTabsAux 0 tabSize rest
      else codePoint :: expandTabsAux (column + 1) tabSize rest

def expandTabs (value : Str) (tabSize : Int := 8) : Str :=
  expandTabsAux 0 tabSize.toNat value

private def splitWhitespaceFuel (unicode : UnicodeData) : Nat → Str → List Str
  | 0, _ => []
  | fuel + 1, value =>
      let trimmed := dropWhile unicode.isWhitespace value
      if trimmed.isEmpty then []
      else
        let word := trimmed.takeWhile fun c => !unicode.isWhitespace c
        word :: splitWhitespaceFuel unicode fuel (trimmed.drop word.length)

def splitWhitespace (unicode : UnicodeData) (value : Str) (maxSplit : Int := -1) : List Str :=
  let fuel := if maxSplit < 0 then value.length + 1 else maxSplit.toNat + 1
  splitWhitespaceFuel unicode fuel value

private def lineBreakLength : Str → Nat
  | 13 :: 10 :: _ => 2
  | c :: _ => if c = 10 || c = 13 || c = 11 || c = 12 ||
      c = 0x1c || c = 0x1d || c = 0x1e || c = 0x85 || c = 0x2028 || c = 0x2029 then 1 else 0
  | [] => 0

private def splitLinesFuel : Nat → Bool → Str → List Str
  | 0, _, value => if value.isEmpty then [] else [value]
  | fuel + 1, keepEnds, value =>
      match value.findIdx? fun _ => false with
      | _ =>
        let position := (List.range (value.length + 1)).find? fun i => lineBreakLength (value.drop i) > 0
        match position with
        | none => if value.isEmpty then [] else [value]
        | some index =>
            let breakLength := lineBreakLength (value.drop index)
            let lineLength := if keepEnds then index + breakLength else index
            value.take lineLength :: splitLinesFuel fuel keepEnds (value.drop (index + breakLength))

def splitLines (value : Str) (keepEnds : Bool := false) : List Str :=
  splitLinesFuel (value.length + 1) keepEnds value

/-- Translation entry: absent means identity, `none` means deletion, and a string means replacement. -/
abbrev TranslationTable := Std.TreeMap CodePoint (Option Str)

def translate (value : Str) (table : TranslationTable) : Str :=
  value.flatMap fun codePoint =>
    match table.get? codePoint with
    | none => [codePoint]
    | some none => []
    | some (some replacement) => replacement

def makeTranslation (entries : List (CodePoint × Option Str)) : TranslationTable :=
  Std.TreeMap.ofList entries

def maketrans (entries : List (CodePoint × Option Str)) : TranslationTable :=
  makeTranslation entries

def encode (codec : Bytes.Codec) (value : Str) : Result Bytes.ByteString := codec.encode value

def fromBytes (codec : Bytes.Codec) (value : Bytes.ByteString) : Result Str := codec.decode value

def fromObject (toString : α → Result Str) (object : α) : Result Str := toString object

/-- Formatting is parameterized by object conversion and format-spec dispatch. -/
structure Formatter (α : Type u) where
  format : Str → List α → List (Str × α) → Result Str

def format (formatter : Formatter α) (template : Str) (args : List α)
    (keywords : List (Str × α) := []) : Result Str := formatter.format template args keywords

def formatMap (formatter : Formatter α) (template : Str)
    (mapping : List (Str × α)) : Result Str := formatter.format template [] mapping

/-- Old-style `%` formatting keeps parsing/conversion policy explicit and type-directed. -/
structure PercentFormatter (α : Type u) where
  format : Str → α → Result Str

def percentFormat (formatter : PercentFormatter α) (template : Str) (arguments : α) : Result Str :=
  formatter.format template arguments

example : chr 97 = .ok [97] := rfl
example : ord [0x20ac] = .ok 0x20ac := rfl
example : zfill [45, 52, 50] 5 = [45, 48, 48, 52, 50] := rfl

end CleanXY.Py.Builtin.Str
