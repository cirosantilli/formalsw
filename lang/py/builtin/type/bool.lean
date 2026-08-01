/-! Exact non-object-identity semantics of Python's two Boolean values. -/

namespace CleanXY.Py.Builtin.Bool

/-- Python has exactly two Boolean values. -/
abbrev BoolValue := Bool

def false : BoolValue := False
def true : BoolValue := True

/-- `bool` is an integer subtype with values zero and one. -/
def toInt (value : BoolValue) : Int := if value then 1 else 0

def not : BoolValue → BoolValue := (!·)

/-- Python `and` returns the second operand only when the first is truthy. -/
def andValue (left : BoolValue) (right : α) (falseValue : α) : α :=
  if left then right else falseValue

/-- Python `or` returns the first truthy operand. -/
def orValue (left : BoolValue) (trueValue right : α) : α :=
  if left then trueValue else right

@[simp] theorem false_toInt : toInt false = 0 := rfl
@[simp] theorem true_toInt : toInt true = 1 := rfl

end CleanXY.Py.Builtin.Bool
