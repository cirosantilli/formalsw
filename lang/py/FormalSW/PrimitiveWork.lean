import lang.py.FormalSW.Runtime

/-! Size-dependent operation charges for an algorithmic cost model.
These are explicit conservative tariffs, not measured CPython timings. Collection
representations must be stated: balanced-tree lookup has logarithmic depth;
collision-chain lookup has linear depth. Unknown operations have no tariff.
Arithmetic policies are separate from collection costs. -/
namespace FormalSW.PyAst.PrimitiveWork

inductive Arithmetic where
  | word
  | bits
deriving DecidableEq

def bitLength (value : Int) : Nat := Nat.log2 value.natAbs + 1

def integer (arithmetic : Arithmetic) (value : Int) : Nat :=
  match arithmetic with
  | .word => 1
  | .bits => bitLength value

/-- Repeated division by a fixed base emits at most one character per input bit,
plus a sign. Fixed arithmetic charges each division once; bit arithmetic charges
the shrinking dividend widths, bounded by the square of the initial width. -/
def decimalOutput (arithmetic : Arithmetic) (value : Int) : Nat :=
  match arithmetic with
  | .word => bitLength value + 1
  | .bits => bitLength value * bitLength value + 1

def scalarSize (arithmetic : Arithmetic) : Constant → Nat
  | .int value => integer arithmetic value
  | .string value => value.length + 1
  | .bytes value => value.length + 1
  | .bool _ | .none => 1

/-- Worst-case comparisons can inspect the whole key, including long strings. -/
def comparison (arithmetic : Arithmetic) (left right : Constant) : Nat :=
  scalarSize arithmetic left + scalarSize arithmetic right

/-- Arithmetic work excludes exponentiation and shifts, which have their own sizes. -/
def integerBinary (arithmetic : Arithmetic) (op : BinOp) (left right : Int) : Option Nat :=
  let width := bitLength left + bitLength right
  match op with
  | .add | .sub | .bitAnd | .bitOr | .bitXor =>
      some (match arithmetic with | .word => 1 | .bits => width)
  | .mult | .floorDiv | .mod =>
      some (match arithmetic with | .word => 1 | .bits => bitLength left * bitLength right)
  | .leftShift => some (match arithmetic with
      | .word => 1
      | .bits => width + right.toNat)
  | .rightShift => some (match arithmetic with | .word => 1 | .bits => width)
  | .pow =>
      if right < 0 then none else
        let iterations := Nat.log2 (right.toNat + 1) + 1
        let resultWidth := bitLength left * (right.toNat + 1) + 1
        some (match arithmetic with
          | .word => iterations
          | .bits => iterations * (resultWidth * resultWidth))

def binary (arithmetic : Arithmetic) (op : BinOp) (left right : Constant) : Option Nat :=
  match scalarNumber left, scalarNumber right with
  | some left, some right => integerBinary arithmetic op left right
  | _, _ => match op, left, right with
      | .add, .string left, .string right => some (left.length + right.length + 1)
      | .add, .bytes left, .bytes right => some (left.length + right.length + 1)
      | .mult, .string text, count | .mult, count, .string text =>
          (scalarNumber count).map fun count => text.length * count.toNat + integer arithmetic count + 1
      | .mult, .bytes bytes, count | .mult, count, .bytes bytes =>
          (scalarNumber count).map fun count => bytes.length * count.toNat + integer arithmetic count + 1
      | _, _, _ => none

inductive MapRepresentation where
  | balancedTree
  | collisionChain
deriving DecidableEq

/-- A comparison-tree tariff, including the empty map and a missing key.
`keyWork` bounds one key comparison; it is not implicitly constant. -/
def mapLookup (representation : MapRepresentation) (entries keyWork : Nat) : Nat :=
  match representation with
  | .balancedTree => (4 * Nat.log2 (entries + 1) + 1) * (keyWork + 1)
  | .collisionChain => (entries + 1) * (keyWork + 1)

def sequenceCopy (length : Nat) : Nat := length + 1

/-- A comparison-sort envelope; comparisons of long keys are charged separately. -/
def comparisonSort (length keyWork : Nat) : Nat :=
  (length + 1) * (Nat.log2 (length + 1) + 1) * (keyWork + 1)

theorem sequenceCopy_positive (length : Nat) : 0 < sequenceCopy length := by
  simp [sequenceCopy]

theorem mapLookup_positive (representation : MapRepresentation) (entries keyWork : Nat) :
    0 < mapLookup representation entries keyWork := by
  cases representation <;> apply Nat.mul_pos <;> omega

end FormalSW.PyAst.PrimitiveWork
