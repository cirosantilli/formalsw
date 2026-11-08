import lang.py.FormalSW.CallsRuntimeCostBitBounds

/-! Common operand budgets for fixed and bit arithmetic. The fixed model still
requires each primitive to have a tariff; library work is accounted for separately. -/
namespace FormalSW.PyAst.Calls.Runtime.NumberBounds
open Scaled

def unit (arithmetic : PrimitiveWork.Arithmetic) (N : Nat) : Nat :=
  match arithmetic with | .word => 4 | .bits => BitBounds.unit N

theorem unit_positive (arithmetic : PrimitiveWork.Arithmetic) (N : Nat) : 1 ≤ unit arithmetic N := by
  cases arithmetic with | word => simp [unit] | bits => exact BitBounds.unit_positive N

theorem unit_two (arithmetic : PrimitiveWork.Arithmetic) (N : Nat) : 2 ≤ unit arithmetic N := by
  cases arithmetic with | word => simp [unit] | bits => exact BitBounds.unit_two N

theorem binary_price (arithmetic : PrimitiveWork.Arithmetic) (N a b : Nat)
    (ha : a ≤ (N+2)^2) (hb : b ≤ (N+2)^2)
    (op : BinOp) (supported : op = .mult ∨ op = .floorDiv ∨ op = .mod ∨ op = .add) :
    ∃ work, PrimitiveWork.binary arithmetic op (.int a) (.int b) = some work ∧ work+1 ≤ unit arithmetic N := by
  cases arithmetic with
  | bits => exact BitBounds.binary_price N a b ha hb op supported
  | word =>
      rcases supported with rfl | rfl | rfl | rfl <;>
        exact ⟨1, rfl, by simp [unit]⟩

theorem compare_price (arithmetic : PrimitiveWork.Arithmetic) (N a b : Nat)
    (ha : a ≤ (N+2)^2) (hb : b ≤ (N+2)^2) :
    PrimitiveWork.comparison arithmetic (.int a) (.int b)+1 ≤ unit arithmetic N := by
  cases arithmetic with
  | bits => exact BitBounds.compare_price N a b ha hb
  | word => exact (by decide : 3 ≤ 4)

theorem next_one (transition : step program state = .next following)
    (priced : Runtime.charge arithmetic program state = some 1)
    (rest : Scaled.Reaches arithmetic program (unit arithmetic N) following budget final) :
    Scaled.Reaches arithmetic program (unit arithmetic N) state (1+budget) final :=
  Scaled.Reaches.next transition ⟨1, priced, unit_positive arithmetic N⟩ rest

theorem mod_cost (arithmetic : PrimitiveWork.Arithmetic) (program : Module) (N n f : Nat) (positive : 0 < f)
    (nb : n ≤ N) (fb : f ≤ N+2) (env : ScalarEnv) (factor : Expr) (getN : env "n" = some (.int n))
    (getF : Scaled.EvaluatesIn arithmetic program (unit arithmetic N) env factor 1 (.int f)) :
    Scaled.EvaluatesIn arithmetic program (unit arithmetic N) env (BitBounds.modTest factor) 9
      (.bool (decide (f ∣ n))) := by
  apply Scaled.EvaluatesIn.compare (unit_positive arithmetic N) (ca := 5) (cb := 1)
    (av := .int (n % f)) (bv := .int 0)
  · exact Scaled.EvaluatesIn.binary (unit_positive arithmetic N)
      (Scaled.EvaluatesIn.lookup (unit_positive arithmetic N) getN) getF
      (by simp [scalarBinary, positive, show f ≠ 0 by omega])
      (binary_price arithmetic N n f (BitBounds.cap N n (by omega)) (BitBounds.cap N f fb) .mod (by simp))
  · exact Scaled.EvaluatesIn.constant (unit_positive arithmetic N)
  · simp [scalarCompare, evalCmpOp, ← Int.dvd_iff_emod_eq_zero, Int.natCast_dvd_natCast]
  · exact compare_price arithmetic N (n%f) 0
      (BitBounds.cap N _ (by have := Nat.mod_le n f; omega)) (BitBounds.cap N 0 (by omega))

end FormalSW.PyAst.Calls.Runtime.NumberBounds
