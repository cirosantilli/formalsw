import lang.py.FormalSW.DecimalWorkBounds
import lang.py.FormalSW.Math

namespace FormalSW.PyAst.PrimitiveWork

/-- A conservative decimal width for a factorial and its intermediate products. -/
def factorialDigits (n : Nat) : Nat := n * ((n+1).log2+1)+1

theorem power_factorial_decimal (n : Nat) : (n+1)^n < 10^(factorialDigits n) := by
  have base : n+1 ≤ 2^((n+1).log2+1) := Nat.le_of_lt Nat.lt_log2_self
  have power := Nat.pow_le_pow_left base n
  rw [← Nat.pow_mul, Nat.mul_comm ((n+1).log2+1)] at power
  exact Nat.lt_of_le_of_lt power (power_two_decimal (n*((n+1).log2+1)))

theorem factorial_le_power (n : Nat) : Math.factorial n ≤ (n+1)^n := by
  induction n with
  | zero => simp [Math.factorial]
  | succ n ih =>
      calc
        Math.factorial (n+1) = (n+1) * Math.factorial n := rfl
        _ ≤ (n+1) * (n+1)^n := Nat.mul_le_mul_left _ ih
        _ ≤ (n+2) * (n+2)^n :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) n)
        _ = (n+2)^(n+1) := by rw [Nat.pow_succ, Nat.mul_comm]

theorem factorial_decimal (n : Nat) : Math.factorial n < 10^(factorialDigits n) :=
  Nat.lt_of_le_of_lt (factorial_le_power n) (power_factorial_decimal n)

end FormalSW.PyAst.PrimitiveWork
