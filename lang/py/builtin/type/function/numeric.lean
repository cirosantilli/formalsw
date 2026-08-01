import lang.py.builtin.type.int

/-! Numeric builtins restricted to their exact integer branches. -/

namespace CleanXY.Py.Builtin.Function.Numeric

open CleanXY.Py.Builtin

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

end CleanXY.Py.Builtin.Function.Numeric
