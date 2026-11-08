import lang.py.FormalSW.DecimalWorkBounds
import lang.py.builtin.type.int

/-! Input measures for algorithms that convert unbounded integers to text.
List length alone does not bound their work, even under fixed arithmetic. -/
namespace FormalSW.PyAst.IntegerListWork
open PrimitiveWork

/-- Python's int.bit_length, including its zero and negative-value conventions. -/
abbrev binarySize (value : Int) : Nat := Py.Builtin.Int.bitLength value

/-- One slot per element, plus the bits in its magnitude. -/
def size (values : List Int) : Nat := (values.map (fun value => binarySize value+1)).sum

theorem size_cons (head : Int) (tail : List Int) :
    size (head :: tail) = binarySize head+1+size tail := rfl

theorem length_le_size (values : List Int) : values.length ≤ size values := by
  induction values with
  | nil => simp [size]
  | cons head tail ih => rw [size_cons]; simp only [List.length_cons]; omega

theorem width_le_slot (value : Int) : bitLength value ≤ binarySize value+1 := by
  by_cases zero : value = 0
  · simp [zero, binarySize, Py.Builtin.Int.bitLength, bitLength]
  · simp [binarySize, Py.Builtin.Int.bitLength, bitLength, zero]

theorem magnitude_lt_power (value : Int) : value.natAbs < 2^binarySize value := by
  by_cases zero : value = 0
  · simp [zero, binarySize, Py.Builtin.Int.bitLength]
  · simpa [binarySize, Py.Builtin.Int.bitLength, zero, bitLength] using (Nat.lt_log2_self (n := value.natAbs))

theorem decimal_value_length (value : Int) :
    (toString value).length ≤ binarySize value+2 := by
  have magnitude := magnitude_lt_power value
  have power : 2^binarySize value ≤ 10^(binarySize value+1) := by
    have base := Nat.pow_le_pow_left (by decide : 2 ≤ 10) (binarySize value)
    rw [Nat.pow_succ]
    omega
  have length := decimal_length value.natAbs (binarySize value+1) (by omega) (by omega)
  have natural : (Nat.repr value.natAbs).length ≤ binarySize value+1 := by
    simpa [Int.repr_eq_if] using length
  have sign : ("-" : String).length = 1 := rfl
  cases value <;> simp [Int.repr_eq_if] at * <;> omega

theorem absolute_sum_lt_power (values : List Int) :
    (values.map Int.natAbs).sum < 2^size values := by
  induction values with
  | nil => simp [size]
  | cons head tail ih =>
      have first := magnitude_lt_power head
      have aPositive : 1 ≤ 2^binarySize head := Nat.one_le_pow _ _ (by decide)
      have bPositive : 1 ≤ 2^size tail := Nat.one_le_pow _ _ (by decide)
      have left := Nat.mul_le_mul_left (2^binarySize head) bPositive
      have right := Nat.mul_le_mul_right (2^size tail) aPositive
      simp only [Nat.mul_one, Nat.one_mul] at left right
      simp only [List.map_cons, List.sum_cons, size_cons, Nat.pow_add, Nat.pow_one]
      rw [Nat.mul_assoc, Nat.mul_comm 2 (2^size tail), ← Nat.mul_assoc]
      omega

theorem fold_magnitude (values : List Int) (initial : Int) :
    (values.foldl Int.add initial).natAbs ≤ initial.natAbs + (values.map Int.natAbs).sum := by
  induction values generalizing initial with
  | nil => simp
  | cons head tail ih =>
      have rest := ih (initial+head)
      have first := Int.natAbs_add_le initial head
      change (tail.foldl Int.add (initial+head)).natAbs ≤
        initial.natAbs+(head.natAbs+(tail.map Int.natAbs).sum)
      omega

theorem sum_width (values : List Int) :
    bitLength (values.foldl Int.add 0) ≤ size values+1 := by
  have magnitude := fold_magnitude values 0
  have total := absolute_sum_lt_power values
  have bounded : (values.foldl Int.add 0).natAbs ≤ 2^size values := by simp at magnitude; omega
  have logarithm := log2_mono bounded
  rw [Nat.log2_two_pow] at logarithm
  exact Nat.add_le_add_right logarithm 1

theorem sum_decimal_length (values : List Int) :
    (toString ((values.foldl Int.add 0).natAbs : Int)).length ≤ size values+1 := by
  have magnitude := fold_magnitude values 0
  have total := absolute_sum_lt_power values
  have power : 2^size values ≤ 10^(size values+1) := by
    have base := Nat.pow_le_pow_left (by decide : 2 ≤ 10) (size values)
    rw [Nat.pow_succ]
    omega
  apply decimal_length _ _ (by omega)
  simp at magnitude
  omega

end FormalSW.PyAst.IntegerListWork
