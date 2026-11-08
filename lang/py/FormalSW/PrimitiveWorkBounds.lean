import lang.py.FormalSW.PrimitiveWork

namespace FormalSW.PyAst.PrimitiveWork

theorem log2_mono {left right : Nat} (ordered : left ≤ right) : left.log2 ≤ right.log2 := by
  by_cases zero : left = 0
  · simp [zero]
  · exact (Nat.le_log2 (by omega : right ≠ 0)).mpr
      (Nat.le_trans (Nat.log2_self_le zero) ordered)

/-- A polynomial bound on values gives a logarithmic bound on their bit widths. -/
theorem bitLength_polynomial (n value degree exponent : Nat)
    (bounded : value ≤ 2 ^ exponent * (n + 1) ^ degree) :
    bitLength (value : Int) ≤ exponent + degree * ((n + 1).log2 + 1) + 1 := by
  have base : n + 1 ≤ 2 ^ ((n + 1).log2 + 1) := Nat.le_of_lt Nat.lt_log2_self
  have power := Nat.mul_le_mul_left (2 ^ exponent) (Nat.pow_le_pow_left base degree)
  rw [← Nat.pow_mul, ← Nat.pow_add] at power
  have logarithm := log2_mono (Nat.le_trans bounded power)
  rw [Nat.log2_two_pow] at logarithm
  simp only [bitLength, Int.natAbs_natCast]
  simpa only [Nat.mul_comm] using Nat.add_le_add_right logarithm 1

/-- For fixed comparison work, balanced-map access has logarithmic growth. -/
theorem balancedLookup_bigO (keyWork : Nat) :
    Growth.IsBigO (fun n => mapLookup .balancedTree n keyWork)
      (fun n => (n+1).log2+1) := by
  refine ⟨4*(keyWork+1), 0, fun n _ => ?_⟩
  have bounded := Nat.mul_le_mul_right (keyWork+1)
    (by omega : 4*(n+1).log2+1 ≤ 4*((n+1).log2+1))
  simpa [mapLookup, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using bounded

/-- Map size cannot be hidden inside a unit-cost transition. -/
theorem balancedLookup_not_constant (keyWork : Nat) :
    ¬ Growth.IsBigO (fun n => mapLookup .balancedTree n keyWork) (fun _ => 1) := by
  rintro ⟨constant, threshold, bounded⟩
  let exponent := constant + threshold + 1
  let n := 2 ^ exponent
  have grows : exponent < n := Nat.lt_two_pow_self
  have large : threshold ≤ n := by dsimp [exponent] at grows; omega
  have depth : exponent ≤ (n+1).log2 :=
    (Nat.le_log2 (by omega : n+1 ≠ 0)).mpr (by dsimp [n]; omega)
  have upper := bounded n large
  have lower := Nat.mul_le_mul_left (4*(n+1).log2+1) (by omega : 1 ≤ keyWork+1)
  simp only [mapLookup, Nat.mul_one] at upper lower
  dsimp [exponent] at depth
  omega

end FormalSW.PyAst.PrimitiveWork
