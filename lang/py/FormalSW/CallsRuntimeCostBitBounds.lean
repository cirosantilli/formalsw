import lang.py.FormalSW.CallsRuntimeCostScaled
import lang.py.FormalSW.PrimitiveWorkBounds

/-! Shared bit-cost budgets for arithmetic on values polynomially bounded by the
input. These lemmas keep the actual primitive tariffs in every source trace. -/
namespace FormalSW.PyAst.Calls.Runtime.BitBounds
open Scaled

def unit (N : Nat) := (5 * ((N + 1).log2 + 1) + 1)^2

theorem unit_positive (N : Nat) : 1 ≤ unit N := by
  have h : 1 ≤ 5*((N+1).log2+1)+1 := by omega
  simpa only [unit, Nat.pow_two] using Nat.le_trans h (Nat.le_mul_self _)

theorem unit_two (N : Nat) : 2 ≤ unit N := by
  have h : 2 ≤ 5*((N+1).log2+1)+1 := by omega
  simpa only [unit, Nat.pow_two] using Nat.le_trans h (Nat.le_mul_self _)

theorem unit_large (N : Nat) : 36 ≤ unit N := by
  have h : 6 ≤ 5*((N+1).log2+1)+1 := by omega
  simpa only [unit, Nat.pow_two] using Nat.mul_le_mul h h

theorem cap (N a : Nat) (bound : a ≤ N + 2) : a ≤ (N+2)^2 := by
  simpa only [Nat.pow_two] using Nat.le_trans bound (Nat.le_mul_self _)

theorem width (N a : Nat) (bound : a ≤ (N+2)^2) :
    PrimitiveWork.bitLength (a : Int) ≤ 5 * ((N+1).log2+1) := by
  have polynomial : a ≤ 2^2 * (N+1)^2 := by
    calc
      a ≤ (N+2)^2 := bound
      _ ≤ (2*(N+1))^2 := Nat.pow_le_pow_left (by omega) 2
      _ = 2^2 * (N+1)^2 := Nat.mul_pow _ _ _
  have estimate := PrimitiveWork.bitLength_polynomial N a 2 2 polynomial
  omega

theorem binary_price (N a b : Nat) (ha : a ≤ (N+2)^2) (hb : b ≤ (N+2)^2)
    (op : BinOp) (supported : op = .mult ∨ op = .floorDiv ∨ op = .mod ∨ op = .add) :
    ∃ work, PrimitiveWork.binary .bits op (.int a) (.int b) = some work ∧ work+1 ≤ unit N := by
  have wa := width N a ha
  have wb := width N b hb
  have product := Nat.mul_le_mul wa wb
  let w := 5*((N+1).log2+1)
  change PrimitiveWork.bitLength (a : Int) ≤ w at wa
  change PrimitiveWork.bitLength (b : Int) ≤ w at wb
  change _ ≤ w*w at product
  rcases supported with rfl | rfl | rfl | rfl <;>
    simp only [PrimitiveWork.binary, scalarNumber, PrimitiveWork.integerBinary] <;>
    refine ⟨_, rfl, ?_⟩ <;> change _ ≤ (w+1)^2 <;>
    simp only [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] <;> omega

theorem compare_price (N a b : Nat) (ha : a ≤ (N+2)^2) (hb : b ≤ (N+2)^2) :
    PrimitiveWork.comparison .bits (.int a) (.int b)+1 ≤ unit N := by
  have wa := width N a ha
  have wb := width N b hb
  let w := 5*((N+1).log2+1)
  change PrimitiveWork.bitLength (a : Int) ≤ w at wa
  change PrimitiveWork.bitLength (b : Int) ≤ w at wb
  change PrimitiveWork.bitLength (a : Int) + PrimitiveWork.bitLength (b : Int) + 1 ≤ (w+1)^2
  simp only [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

theorem next_one (transition : step program state = .next following)
    (priced : Runtime.charge .bits program state = some 1)
    (rest : Scaled.Reaches .bits program (unit N) following budget final) :
    Scaled.Reaches .bits program (unit N) state (1+budget) final :=
  Scaled.Reaches.next transition ⟨1, priced, unit_positive N⟩ rest

def modTest (factor : Expr) : Expr :=
  .compare (.binOp (.name "n") .mod factor) [(.eq, .constant (.int 0))]

theorem mod_cost (program : Module) (N n f : Nat) (positive : 0 < f)
    (nb : n ≤ N) (fb : f ≤ N+2)
    (env : ScalarEnv) (factor : Expr) (getN : env "n" = some (.int n))
    (getF : Scaled.EvaluatesIn .bits program (unit N) env factor 1 (.int f)) :
    Scaled.EvaluatesIn .bits program (unit N) env (modTest factor) 9 (.bool (decide (f ∣ n))) := by
  apply Scaled.EvaluatesIn.compare (unit_positive N) (ca := 5) (cb := 1) (av := .int (n % f)) (bv := .int 0)
  · exact Scaled.EvaluatesIn.binary (unit_positive N) (Scaled.EvaluatesIn.lookup (unit_positive N) getN) getF
      (by simp [scalarBinary, positive, show f ≠ 0 by omega])
      (binary_price N n f (cap N n (by omega)) (cap N f fb) .mod (by simp))
  · exact Scaled.EvaluatesIn.constant (unit_positive N)
  · simp [scalarCompare, evalCmpOp, ← Int.dvd_iff_emod_eq_zero, Int.natCast_dvd_natCast]
  · exact compare_price N (n%f) 0 (cap N _ (by have := Nat.mod_le n f; omega)) (cap N 0 (by omega))

end FormalSW.PyAst.Calls.Runtime.BitBounds
