import lang.py.FormalSW.PrimitiveWork

/-! A grow-only dynamic array doubles capacity when full. Its semantic contents
do not store unused slots. Copying during a resize is charged explicitly; the
potential proof, rather than a unit-cost assumption, bounds repeated appends.
This is an abstract array representation, not CPython's exact growth schedule. -/
namespace FormalSW.PyAst.PrimitiveWork.DynamicArray

def capacity : Nat → Nat
  | 0 => 0
  | n + 1 => if capacity n ≤ n then max 1 (2 * capacity n) else capacity n

theorem capacity_bounds (n : Nat) : n ≤ capacity n ∧ capacity n ≤ 2 * n := by
  induction n with
  | zero => simp [capacity]
  | succ n ih =>
      simp only [capacity]
      split <;> omega

/-- One element write, and a copy of the old contents only when the array is full. -/
def append (length : Nat) : Nat :=
  1 + if capacity length ≤ length then length else 0

def potential (length : Nat) : Nat := 2 * length - capacity length

theorem potential_le (n : Nat) : potential n ≤ n := by
  have := capacity_bounds n
  unfold potential
  omega

/-- Three units per append pay for every resize, starting with an empty array. -/
theorem append_amortized (n : Nat) :
    append n + potential (n + 1) ≤ 3 + potential n := by
  have := capacity_bounds n
  simp only [append, potential, capacity]
  split <;> omega

def appendMany (start : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => appendMany start count + append (start + count)

theorem appendMany_amortized (start count : Nat) :
    appendMany start count + potential (start + count) ≤ 3 * count + potential start := by
  induction count with
  | zero => simp [appendMany]
  | succ count ih =>
      have := append_amortized (start + count)
      simp only [appendMany, Nat.mul_succ, ← Nat.add_assoc]
      omega

theorem appendMany_empty (count : Nat) : appendMany 0 count ≤ 3 * count := by
  have := appendMany_amortized 0 count
  simp only [potential, capacity, Nat.mul_zero, Nat.sub_self, Nat.add_zero] at this
  omega

end FormalSW.PyAst.PrimitiveWork.DynamicArray
