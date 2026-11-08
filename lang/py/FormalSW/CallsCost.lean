import lang.py.FormalSW.Calls
import lang.py.FormalSW.ExecutionCost

/-! Compositional transition costs for scalar Python calls and range sums. -/
namespace FormalSW.PyAst.Calls.Cost

/-- Expression cost is independent of the caller's continuation. -/
def EvaluatesIn (module : Module) (env : ScalarEnv) (expression : Expr)
    (cost : Nat) (value : Constant) : Prop :=
  ∀ stack, ReachesIn (step module) ⟨.expr expression env, stack⟩ cost ⟨.value value, stack⟩

namespace EvaluatesIn

theorem constant : EvaluatesIn module env (.constant value) 1 value :=
  fun _ => .next rfl .refl

theorem lookup (found : env name = some value) : EvaluatesIn module env (.name name) 1 value :=
  fun _ => .next (by simp [step, outcome, found]) .refl

theorem binary (left : EvaluatesIn module env a ca av)
    (right : EvaluatesIn module env b cb bv)
    (result : scalarBinary op av bv = some (.ok value)) :
    EvaluatesIn module env (.binOp a op b) (ca + cb + 3) value := by
  intro stack
  have run := ReachesIn.next (step := step module) (state := ⟨.expr (.binOp a op b) env, stack⟩)
    rfl ((left _).trans (.next rfl ((right _).trans (.next (following := ⟨.value value, stack⟩) (by simp [step, outcome, result]) .refl))))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

end EvaluatesIn

/-- Count every iteration of an unfiltered range sum, including evaluation of its
item expression. The proof applies in any continuation, including a helper call. -/
theorem rangeSum (module : Module) (sum : RangeSum) (item : Int → Int) (itemCost : Nat)
    (unfiltered : sum.conditions = []) (stride : sum.stride = 1)
    (evaluated : ∀ i, EvaluatesIn module (sum.env.set sum.name (.int i)) sum.element itemCost (.int (item i)))
    (remaining : Nat) (start total : Int) (stop : sum.stop = start + remaining)
    (stack : List Frame) :
    ∃ answer, ReachesIn (step module) ⟨.sumLoop sum start total, stack⟩
      ((itemCost + 4) * remaining + 1) ⟨.value (.int answer), stack⟩ := by
  induction remaining generalizing start total with
  | zero =>
      refine ⟨total, .next ?_ .refl⟩
      simp [step, rangeContinues, stop, stride]
  | succ remaining ih =>
      obtain ⟨answer, rest⟩ := ih (start + 1) (total + item start) (by simp_all; omega)
      refine ⟨answer, ?_⟩
      have continues : rangeContinues start sum.stop sum.stride = true := by
        simp [rangeContinues, stop, stride]
        omega
      have first : step module ⟨.sumLoop sum start total, stack⟩ =
          .next ⟨.expr (.constant (.bool true)) (sum.env.set sum.name (.int start)),
            .sumFilter sum start total :: stack⟩ := by
        simp [step, continues, RangeSum.filter, unfiltered]
      have afterItem : step module ⟨.value (.int (item start)), .sumElement sum start total :: stack⟩ =
          .next ⟨.sumLoop sum (start + 1) (total + item start), stack⟩ := by
        simp [step, sumAdd, stride]
      have run := ReachesIn.next first (.next rfl (.next rfl
        ((evaluated start _).trans (.next afterItem rest))))
      have costEq : (itemCost + 4) * (remaining + 1) + 1 =
          itemCost + ((itemCost + 4) * remaining + 1 + 1) + 1 + 1 + 1 := by
        rw [Nat.mul_succ]
        omega
      rw [costEq]
      exact run

end FormalSW.PyAst.Calls.Cost
