import lang.py.builtin.type.bool
import lang.py.builtin.type.core
import lang.py.builtin.type.descriptor
import lang.py.builtin.type.dict
import lang.py.builtin.type.int
import lang.py.builtin.type.iterator
import lang.py.builtin.type.list
import lang.py.builtin.type.special
import lang.py.builtin.type.str
import lang.py.builtin.type.type
import Init.Data.Nat.ToString
import Lean.Elab.Tactic.Omega

/-! Python builtin function semantics, kept in one module. -/



namespace FormalSW.Py.Builtin.Function.Conversion

open FormalSW.Py.Builtin

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

private theorem digit_eq_digitChar (value : Nat) (small : value < 16) :
    digit value = (Nat.digitChar value).toNat := by
  by_cases decimal : value < 10
  · simp only [digit, if_pos decimal, Nat.toNat_digitChar_of_lt_ten decimal]
  · have choices : value = 10 ∨ value = 11 ∨ value = 12 ∨ value = 13 ∨ value = 14 ∨ value = 15 := by omega
    rcases choices with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem digitsFuel_eq_toDigits (base fuel value : Nat)
    (baseLower : 1 < base) (baseUpper : base ≤ 16) (enough : value < fuel) :
    digitsFuel base fuel value = (Nat.toDigits base value).map Char.toNat := by
  induction fuel generalizing value with
  | zero => omega
  | succ fuel ih =>
      rw [digitsFuel, Nat.toDigits_eq_if baseLower]
      by_cases small : value < base
      · simp only [if_pos small, List.map_cons, List.map_nil,
          digit_eq_digitChar value (by omega)]
      · have decreases : value / base < value := Nat.div_lt_self (by omega) baseLower
        have next := ih (value / base) (by omega)
        have remainder : value % base < 16 :=
          Nat.lt_of_lt_of_le (Nat.mod_lt value (by omega : 0 < base)) baseUpper
        simp only [if_neg small, List.map_append, List.map_cons, List.map_nil,
          next, digit_eq_digitChar (value % base) remainder]

private theorem formatUnsigned_eq_toDigits (base value : Nat)
    (baseLower : 1 < base) (baseUpper : base ≤ 16) :
    formatUnsigned base value = (Nat.toDigits base value).map Char.toNat := by
  by_cases zero : value = 0
  · subst value
    simp [formatUnsigned]
  · simp only [formatUnsigned, if_neg zero]
    exact digitsFuel_eq_toDigits base (value+1) value baseLower baseUpper (Nat.lt_succ_self _)

/-- The standard binary prefix precedes the full, untruncated numeral. -/
theorem bin_nat (value : Nat) :
    bin (value : Int) = [48, 98] ++ (Nat.toDigits 2 value).map Char.toNat := by
  simp only [bin, formatInteger, show ¬ (value : Int) < 0 by omega, if_false,
    List.nil_append, Int.natAbs_natCast]
  rw [formatUnsigned_eq_toDigits 2 value (by decide) (by decide)]

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

end FormalSW.Py.Builtin.Function.Conversion


namespace FormalSW.Py.Builtin.Function.Iterable

open FormalSW.Py.Builtin

def all (truth : α → Bool) (values : List α) : Bool := values.all truth
def any (truth : α → Bool) (values : List α) : Bool := values.any truth
def len (values : List α) : Nat := values.length
def iter (values : List α) : Iterator.Iterator α := Iterator.ofList values
def aiter (values : List α) : Iterator.AsyncIterator α := ⟨values⟩
def next (iterator : Iterator.Iterator α) : Result (α × Iterator.Iterator α) :=
  Iterator.next iterator
def nextD (iterator : Iterator.Iterator α) (default : α) : α × Iterator.Iterator α :=
  Iterator.nextD iterator default
def anext (iterator : Iterator.AsyncIterator α) : Result (α × Iterator.AsyncIterator α) :=
  Iterator.anext iterator
def anextD (iterator : Iterator.AsyncIterator α) (default : α) : α × Iterator.AsyncIterator α :=
  Iterator.anextD iterator default
def reversed (values : List α) : Iterator.Iterator α := Iterator.reversed values

def enumerate (values : List α) (start : Int := 0) : Iterator.Iterator (Int × α) :=
  Iterator.ofList (values.mapIdx fun index value => (start + index, value))

def filter (predicate : α → Bool) (values : List α) : Iterator.Iterator α :=
  Iterator.ofList (values.filter predicate)
def map (function : α → β) (values : List α) : Iterator.Iterator β :=
  Iterator.ofList (values.map function)

/-- Two-argument `iter(callable, sentinel)`, bounded by explicit execution fuel. -/
private def iterSentinelFuel [BEq α] (call : State → Result (α × State))
    (sentinel : α) : Nat → State → Result (List α × State)
  | 0, state => .ok ([], state)
  | fuel + 1, state => do
      let (value, nextState) ← call state
      if value == sentinel then return ([], nextState)
      let (rest, finalState) ← iterSentinelFuel call sentinel fuel nextState
      return (value :: rest, finalState)

def iterSentinel [BEq α] (call : State → Result (α × State)) (sentinel : α)
    (fuel : Nat) (state : State) : Result (List α × State) :=
  iterSentinelFuel call sentinel fuel state

private def choose (better : α → α → Bool) : List α → Option α
  | [] => none
  | first :: rest =>
      some (rest.foldl (fun best candidate => if better candidate best then candidate else best) first)

def max? (less : α → α → Bool) (values : List α) : Option α :=
  choose (fun candidate best => less best candidate) values

def min? (less : α → α → Bool) (values : List α) : Option α := choose less values

def max (less : α → α → Bool) (values : List α) : Result α :=
  match max? less values with
  | some value => .ok value
  | none => .error (.valueError "max() iterable argument is empty")

def min (less : α → α → Bool) (values : List α) : Result α :=
  match min? less values with
  | some value => .ok value
  | none => .error (.valueError "min() iterable argument is empty")

def maxD (less : α → α → Bool) (values : List α) (default : α) : α :=
  (max? less values).getD default
def minD (less : α → α → Bool) (values : List α) (default : α) : α :=
  (min? less values).getD default

def maxKey? (key : α → β) (less : β → β → Bool) (values : List α) : Option α :=
  choose (fun candidate best => less (key best) (key candidate)) values
def minKey? (key : α → β) (less : β → β → Bool) (values : List α) : Option α :=
  choose (fun candidate best => less (key candidate) (key best)) values

/-- Stable `sorted`, sharing the list model's strict-less insertion sort. -/
def sorted (less : α → α → Bool) (values : List α) (reverse : Bool := false) : List α :=
  List.sort values less reverse

def sortedKey (key : α → β) (less : β → β → Bool) (values : List α)
    (reverse : Bool := false) : List α :=
  List.sort values (fun left right => less (key left) (key right)) reverse

private def allEmpty : List (List α) → Bool
  | [] => true
  | values :: rest => values.isEmpty && allEmpty rest

private def anyEmpty : List (List α) → Bool
  | [] => false
  | values :: rest => values.isEmpty || anyEmpty rest

private def heads : List (List α) → Option (List α)
  | [] => some []
  | [] :: _ => none
  | (value :: _) :: rest => (value :: ·) <$> heads rest

private def tails : List (List α) → List (List α)
  | [] => []
  | [] :: rest => [] :: tails rest
  | (_ :: tail) :: rest => tail :: tails rest

private def zipFuel : Nat → List (List α) → Bool → Result (List (List α))
  | 0, _, _ => .ok []
  | fuel + 1, iterables, strict =>
      if allEmpty iterables then .ok []
      else if anyEmpty iterables then
        if strict then .error (.valueError "zip() arguments have different lengths") else .ok []
      else do
        let row ← match heads iterables with
          | some row => .ok row
          | none => .error (.runtimeError "invalid zip iterator state")
        return row :: (← zipFuel fuel (tails iterables) strict)

/-- Python `zip`, including the `strict=True` length check. -/
private def zipValues (iterables : List (List α)) (strict : Bool := false) : Result (List (List α)) :=
  let fuel := iterables.foldl (fun largest values => Nat.max largest values.length) 0
  zipFuel fuel iterables strict

def zip (iterables : List (List α)) (strict : Bool := false) :
    Result (Iterator.Iterator (List α)) :=
  Iterator.ofList <$> zipValues iterables strict

/-- Multi-iterable `map`, including Python 3.14's `strict` option. -/
def mapMany (function : List α → β) (iterables : List (List α))
    (strict : Bool := false) : Result (List β) := do
  return (← zipValues iterables strict).map function

example : enumerate [10, 20] 3 = ⟨[(3, 10), (4, 20)]⟩ := rfl
example : zip [[1, 2], [3, 4]] = .ok ⟨[[1, 3], [2, 4]]⟩ := rfl
example : zip [[1], [2, 3]] true = .error (.valueError "zip() arguments have different lengths") := rfl

end FormalSW.Py.Builtin.Function.Iterable


namespace FormalSW.Py.Builtin.Function.Numeric

open FormalSW.Py.Builtin

def abs (number : Int) : Int := Int.natAbs number
def divmod (left right : Int) : Result (Int × Int) := Int.divMod left right
def pow (base exponent : Int) : Result Int := Int.pow base exponent
def powMod (base exponent modulus : Int) : Result Int := Int.powMod base exponent modulus

/-- Sum an integer iterable from an integer starting value. -/
def sum (values : List Int) (start : Int := 0) : Int := values.foldl (· + ·) start

/-- Integer `round`, including negative digits and Python's ties-to-even rule. -/
def round (number : Int) (ndigits : Option Int := none) : Result Int :=
  match ndigits with
  | none => .ok number
  | some digits =>
      if digits ≥ 0 then .ok number
      else
        let factor := (10 : Int) ^ (-digits).toNat
        let quotient := Int.fdiv number factor
        let remainder := number - quotient * factor
        let doubled := 2 * remainder
        if doubled < factor then .ok (quotient * factor)
        else if doubled > factor then .ok ((quotient + 1) * factor)
        else if quotient % 2 = 0 then .ok (quotient * factor)
        else .ok ((quotient + 1) * factor)

example : round 25 (some (-1)) = .ok 20 := rfl
example : round 35 (some (-1)) = .ok 40 := rfl
example : round (-25) (some (-1)) = .ok (-20) := rfl

end FormalSW.Py.Builtin.Function.Numeric


namespace FormalSW.Py.Builtin.Function.Protocol

open FormalSW.Py.Builtin

structure IndexProtocol (α : Type u) where
  index : α → Result Int

structure AbsProtocol (α : Type u) (ResultType : Type v) where
  abs : α → Result ResultType

structure LengthProtocol (α : Type u) where
  length : α → Result Int

structure IterProtocol (α : Type u) (Element : Type v) where
  iter : α → Result (Iterator.Iterator Element)

structure AsyncIterProtocol (α : Type u) (Element : Type v) where
  aiter : α → Result (Iterator.AsyncIterator Element)

structure ReversedProtocol (α : Type u) (Element : Type v) where
  reversed : α → Result (Iterator.Iterator Element)

structure RoundProtocol (α : Type u) (ResultType : Type v) where
  round : α → Option Int → Result ResultType

structure DirProtocol (α : Type u) where
  dir : α → Result (List String)

structure BinaryNumericProtocol (α : Type u) (ResultType : Type v) where
  divmod : α → α → Result ResultType
  pow : α → α → Option α → Result ResultType

def absObject (protocol : AbsProtocol α ResultType) (object : α) : Result ResultType :=
  protocol.abs object
def indexObject (protocol : IndexProtocol α) (object : α) : Result Int := protocol.index object
def lenObject (protocol : LengthProtocol α) (object : α) : Result Nat := do
  let length ← protocol.length object
  if length < 0 then .error (.valueError "__len__() should return >= 0")
  else return length.toNat
def iterObject (protocol : IterProtocol α Element) (object : α) := protocol.iter object
def aiterObject (protocol : AsyncIterProtocol α Element) (object : α) := protocol.aiter object
def reversedObject (protocol : ReversedProtocol α Element) (object : α) := protocol.reversed object
def roundObject (protocol : RoundProtocol α ResultType) (object : α) (digits : Option Int := none) :=
  protocol.round object digits
def dirObject (protocol : DirProtocol α) (object : α) := protocol.dir object
def divmodObject (protocol : BinaryNumericProtocol α ResultType) (left right : α) :=
  protocol.divmod left right
def powObject (protocol : BinaryNumericProtocol α ResultType) (base exponent : α)
    (modulus : Option α := none) := protocol.pow base exponent modulus

end FormalSW.Py.Builtin.Function.Protocol


namespace FormalSW.Py.Builtin.Function.Reflection

open FormalSW.Py.Builtin

def callable (object : Object.Object α) : Bool := Object.isCallable object
def delattr (object : Object.Object α) (name : String) := Object.delAttr object name
def dir (object : Object.Object α) : List String := Object.dir object
def getattr? (object : Object.Object α) (name : String) : Option α := Object.getAttr? object name
def getattrD (object : Object.Object α) (name : String) (default : α) : α :=
  (Object.getAttr? object name).getD default
def getattr (object : Object.Object α) (name : String) : Result α :=
  match Object.getAttr? object name with
  | some value => .ok value
  | none => .error (.attributeError s!"object has no attribute '{name}'")
def hasattr (object : Object.Object α) (name : String) : Bool := Object.hasAttr object name
def id (object : Object.Object α) : Nat := Object.id object
def setattr (object : Object.Object α) (name : String) (value : α) :=
  Object.setAttr object name value
def vars (object : Object.Object α) := Object.vars object
def hash (model : Object.HashModel α) (object : α) : Int := model.hash object

def isinstance (registry : Type.Registry) (object : Object.Object α) (typeId : Nat) : Bool :=
  Type.isInstance registry object typeId
def isinstanceAny (registry : Type.Registry) (object : Object.Object α)
    (typeIds : List Nat) : Bool := typeIds.any (Type.isInstance registry object)
def issubclass (registry : Type.Registry) (candidate target : Nat) : Bool :=
  Type.isSubclass registry candidate target
def issubclassAny (registry : Type.Registry) (candidate : Nat) (targets : List Nat) : Bool :=
  targets.any (Type.isSubclass registry candidate)
def type? (registry : Type.Registry) (object : Object.Object α) := Type.typeOf? registry object

def classmethod (function : Class → Args → ResultType) :
    Descriptor.ClassMethod Class Args ResultType := ⟨function⟩

def staticmethod (function : Args → ResultType) : Descriptor.StaticMethod Args ResultType :=
  ⟨function⟩

end FormalSW.Py.Builtin.Function.Reflection


namespace FormalSW.Py.Builtin.Function.Runtime

open FormalSW.Py.Builtin

abbrev Namespace (α : Type u) := Dict.Dict String α

structure RuntimeState (α : Type u) where
  globals : Namespace α := Dict.empty
  locals : Namespace α := Dict.empty
  standardOutput : Str.Str := []
  standardError : Str.Str := []
  standardInput : List Str.Str := []

inductive CompileMode where
  | exec
  | eval
  | single
deriving Repr, DecidableEq

def compile (source filename : String) (mode : CompileMode) (flags : Nat := 0)
    (optimization : Int := -1) : Special.CodeObject :=
  { source, filename,
    mode := match mode with | .exec => "exec" | .eval => "eval" | .single => "single"
    flags, optimization }

structure Evaluator (α : Type u) where
  eval : Special.CodeObject → Namespace α → Namespace α → Result α
  exec : Special.CodeObject → Namespace α → Namespace α → Result (Namespace α × Namespace α)

def eval (evaluator : Evaluator α) (code : Special.CodeObject)
    (state : RuntimeState α) : Result α := evaluator.eval code state.globals state.locals

def exec (evaluator : Evaluator α) (code : Special.CodeObject)
    (state : RuntimeState α) : Result (RuntimeState α) := do
  let (globals, locals) ← evaluator.exec code state.globals state.locals
  return { state with globals := globals, locals := locals }

def globals (state : RuntimeState α) : Namespace α := state.globals
def locals (state : RuntimeState α) : Namespace α := state.locals

def print (render : α → Result Str.Str) (objects : List α) (state : RuntimeState α)
    (separator : Str.Str := [32]) (ending : Str.Str := [10]) : Result (RuntimeState α) := do
  let rendered ← objects.mapM render
  let output := Subsequence.join separator rendered ++ ending
  return { state with standardOutput := state.standardOutput ++ output }

def input (state : RuntimeState α) (prompt : Str.Str := []) : Result (Str.Str × RuntimeState α) :=
  match state.standardInput with
  | [] => .error .eofError
  | line :: rest =>
      .ok (line, { state with
        standardInput := rest
        standardOutput := state.standardOutput ++ prompt })

structure FileSystem (Handle : Type u) where
  openFile : String → String → Result Handle

def «open» (filesystem : FileSystem Handle) (path mode : String) : Result Handle :=
  filesystem.openFile path mode

structure ImportSystem (Module : Type u) where
  importModule : String → List String → Int → Result Module

def «__import__» (system : ImportSystem Module) (name : String)
    (fromList : List String := []) (level : Int := 0) : Result Module :=
  system.importModule name fromList level

structure HelpSystem (α : Type u) where
  render : Option α → Result Str.Str

def help (system : HelpSystem α) (object : Option α := none) : Result Str.Str := system.render object

structure BreakpointHook (Args : Type u) (ResultType : Type v) where
  call : Args → Result ResultType

def breakpoint (hook : BreakpointHook Args ResultType) (args : Args) : Result ResultType :=
  hook.call args

end FormalSW.Py.Builtin.Function.Runtime
