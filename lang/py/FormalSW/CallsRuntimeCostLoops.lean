import lang.py.FormalSW.Calls
import lang.py.FormalSW.CallsRuntimeCost

/-! Compositional runtime costs for scalar expressions and fixed-arithmetic range sums. -/
namespace FormalSW.PyAst.Calls.Runtime

/-- Expression cost is independent of the caller's continuation. -/
def EvaluatesIn (arithmetic : PrimitiveWork.Arithmetic) (module : Module) (env : ScalarEnv) (expression : Expr)
    (cost : Nat) (value : Constant) : Prop :=
  ∀ stack, RuntimeCost.Reaches (step module) (charge arithmetic module) ⟨.expr expression env, stack⟩ cost ⟨.value value, stack⟩

namespace EvaluatesIn

theorem constant : EvaluatesIn arithmetic module env (.constant value) 1 value := by
  intro stack
  exact .next (amount := 1) (cost := 0) rfl rfl .refl

theorem lookup (found : env name = some value) : EvaluatesIn arithmetic module env (.name name) 1 value := by
  intro stack
  exact .next (amount := 1) (cost := 0) (by simp [step, outcome, found]) rfl .refl

theorem binary (left : EvaluatesIn arithmetic module env a ca av)
    (right : EvaluatesIn arithmetic module env b cb bv)
    (result : scalarBinary op av bv = some (.ok value))
    (measured : PrimitiveWork.binary arithmetic op av bv = some work) :
    EvaluatesIn arithmetic module env (.binOp a op b) (ca + cb + work + 3) value := by
  intro stack
  have run := RuntimeCost.Reaches.next (charge := charge arithmetic module) (step := step module) (state := ⟨.expr (.binOp a op b) env, stack⟩)
    rfl rfl ((left _).trans (.next rfl rfl ((right _).trans (.next (amount := work + 1) (following := ⟨.value value, stack⟩) (by simp [step, outcome, result]) (by simp [charge, measured]) .refl))))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

end EvaluatesIn

/-- Count every iteration of an unfiltered range sum, including evaluation of its
item expression. The proof applies in any continuation, including a helper call. -/
theorem rangeSum (module : Module) (sum : RangeSum) (item : Int → Int) (itemCost : Nat)
    (unfiltered : sum.conditions = []) (stride : sum.stride = 1)
    (evaluated : ∀ i, EvaluatesIn .word module (sum.env.set sum.name (.int i)) sum.element itemCost (.int (item i)))
    (remaining : Nat) (start total : Int) (stop : sum.stop = start + remaining)
    (stack : List Frame) :
    ∃ answer, RuntimeCost.Reaches (step module) (charge .word module) ⟨.sumLoop sum start total, stack⟩
      ((itemCost + 13) * remaining + 4) ⟨.value (.int answer), stack⟩ := by
  induction remaining generalizing start total with
  | zero =>
      refine ⟨total, .next (amount := 4) (cost := 0) ?_ rfl .refl⟩
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
      have run := RuntimeCost.Reaches.next (charge := charge .word module) first rfl (.next rfl rfl (.next rfl rfl
        ((evaluated start _).trans (.next afterItem rfl rest))))
      have costEq : (itemCost + 13) * (remaining + 1) + 4 =
          4 + (1 + (3 + (itemCost + (5 + ((itemCost + 13) * remaining + 4))))) := by
        rw [Nat.mul_succ]
        omega
      rw [costEq]
      exact run


end FormalSW.PyAst.Calls.Runtime
