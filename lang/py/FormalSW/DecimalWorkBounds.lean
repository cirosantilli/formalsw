import lang.py.FormalSW.PrimitiveWorkBounds
import Init.Data.Nat.ToString
import Init.Data.Int.ToString

namespace FormalSW.PyAst.PrimitiveWork

/-- A decimal digit bound also bounds the work of integer-to-string conversion. -/
theorem bitLength_decimal (value digits : Nat) (bounded : value < 10^digits) :
    bitLength (value : Int) ≤ 4*digits+1 := by
  have power := Nat.pow_le_pow_left (by decide : 10 ≤ 2^4) digits
  rw [← Nat.pow_mul] at power
  have logarithm := log2_mono (Nat.le_trans (Nat.le_of_lt bounded) power)
  rw [Nat.log2_two_pow] at logarithm
  simpa only [bitLength, Int.natAbs_natCast] using Nat.add_le_add_right logarithm 1

theorem decimal_length (value digits : Nat) (positive : 0 < digits) (bounded : value < 10^digits) :
    (toString (value : Int)).length ≤ digits := by
  simpa [Int.repr_eq_if] using (Nat.length_repr_le_iff positive).mpr bounded

end FormalSW.PyAst.PrimitiveWork
