import lang.py.FormalSW.ScalarSets

/-! Immutable builtin keys separate Python equality from stored representation.
Sets keep the original value alongside its key; a tuple key is not a copy of the
tuple object and never replaces its reference in the observable heap. -/
namespace FormalSW.PyAst

inductive HashKey where
  | scalar (value : Constant)
  | tuple (items : List HashKey)
deriving Repr, BEq

namespace HashKey

mutual
  private def decideKey : (left right : HashKey) → Decidable (left = right)
    | .scalar left, .scalar right =>
        match decEq left right with
        | .isTrue same => .isTrue (by cases same; rfl)
        | .isFalse different => .isFalse (by intro same; cases same; exact different rfl)
    | .tuple left, .tuple right =>
        match decideKeys left right with
        | .isTrue same => .isTrue (by cases same; rfl)
        | .isFalse different => .isFalse (by intro same; cases same; exact different rfl)
    | .scalar _, .tuple _ => .isFalse (by intro same; cases same)
    | .tuple _, .scalar _ => .isFalse (by intro same; cases same)
  private def decideKeys : (left right : List HashKey) → Decidable (left = right)
    | [], [] => .isTrue rfl
    | [], _ :: _ => .isFalse (by intro same; cases same)
    | _ :: _, [] => .isFalse (by intro same; cases same)
    | left :: lefts, right :: rights =>
        match decideKey left right with
        | .isFalse different => .isFalse (by intro same; cases same; exact different rfl)
        | .isTrue same => match decideKeys lefts rights with
            | .isFalse different => .isFalse (by intro same; cases same; exact different rfl)
            | .isTrue rest => .isTrue (by cases same; cases rest; rfl)
end

instance : DecidableEq HashKey := decideKey

mutual
  def depth : HashKey → Nat
    | .scalar _ => 1
    | .tuple items => listDepth items + 1
  def listDepth : List HashKey → Nat
    | [] => 0
    | item :: rest => max (depth item) (listDepth rest)
end

def equalFuel : Nat → HashKey → HashKey → Bool
  | 0, _, _ => false
  | fuel + 1, .tuple left, .tuple right => left.isEqv right (equalFuel fuel)
  | _ + 1, .scalar left, .scalar right => (scalarCompare .eq left right).getD false
  | _ + 1, _, _ => false

/-- Numeric scalar equality identifies Bool and Int representatives recursively. -/
def equal (left right : HashKey) : Bool := equalFuel (left.depth + right.depth + 1) left right

def typeName : HashKey → String
  | .scalar value => (Data.scalar value).typeName
  | .tuple _ => "tuple"

def beforeFuel : Nat → HashKey → HashKey → Bool
  | 0, _, _ => false
  | fuel + 1, .tuple left, .tuple right => left.lex right (beforeFuel fuel)
  | _ + 1, .scalar left, .scalar right => ScalarSet.before left right
  | _ + 1, left, right => decide (left.typeName < right.typeName)

/-- Observation orders keys by their actual types and values, retaining the
first inserted representative even when Python equality identifies two types. -/
def before (left right : HashKey) : Bool := beforeFuel (left.depth + right.depth + 1) left right

@[simp] theorem equal_scalars (left right : Constant) :
    equal (.scalar left) (.scalar right) = (scalarCompare .eq left right).getD false := rfl

@[simp] theorem before_scalars (left right : Constant) :
    before (.scalar left) (.scalar right) = ScalarSet.before left right := rfl

end HashKey
end FormalSW.PyAst
