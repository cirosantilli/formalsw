import FormalSW
import lang.py.FormalSW.MemoCallRules

namespace MemoCallTests
open FormalSW.PyAst FormalSW.PyAst.MemoCalls

private def program : Module := { body := [
  .functionDef "count" [{ name := "n", annotation := some (.name "int") }] (some (.name "int")) [
    .ifThen (.compare (.name "n") [(.ltE, .constant (.int 0))]) [.return (.constant (.int 0))] [],
    .return (.binOp (.constant (.int 1)) .add
      (.call (.name "count") [.binOp (.name "n") .sub (.constant (.int 1))]))]] }

private def spec (key : Key) (value : Constant) : Prop :=
  ∃ n : Nat, key = ⟨"count", [n]⟩ ∧ value = .int n

private theorem count_body (n : Nat) :
    ReturnsValue program ["count"] spec "count" [.int n] (.int n) := by
  induction n with
  | zero =>
      apply BlockReturns.memoized_function (values := [0]) (by simp) rfl rfl
      · apply BlockReturns.branch (value := .bool true)
        · exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant rfl
        · exact BlockReturns.return_value Evaluates.constant
      · exact ⟨0, rfl, rfl⟩
      · rintro other ⟨k, same, rfl⟩
        have equalInt : (0 : Int) = k := by simpa [Key.mk.injEq] using same
        have zero : k = 0 := by omega
        simp [zero]
  | succ n ih =>
      apply BlockReturns.memoized_function (values := [n + 1]) (by simp) rfl rfl
      · apply BlockReturns.branch (value := .bool false)
        · apply Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
          simp [scalarCompare, evalCmpOp]
        · apply BlockReturns.return_value
          apply Evaluates.binary (av := .int 1) (bv := .int n)
          · exact Evaluates.constant
          · apply Evaluates.call (values := [.int n])
            · exact .cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant
                (by simp [scalarBinary])) .nil
            · exact ih
          · simp [scalarBinary, Int.add_comm]
      · exact ⟨n + 1, rfl, rfl⟩
      · rintro other ⟨k, same, rfl⟩
        have equalInt : (k : Int) = n + 1 := by simpa [Key.mk.injEq, eq_comm] using same
        have equal : k = n + 1 := by omega
        simp [equal]

/-- Recursion terminates for every natural input, with any already correct cache. -/
theorem count_returns (n : Nat) (cache : Cache) (valid : cache.Valid spec) :
    (function program ["count"] "count" [.int n] cache).Returns :=
  (count_body n).returns_cached valid

example (n : Nat) : (function program ["count"] "count" [.int n]).Returns :=
  (count_body n).returns

end MemoCallTests
