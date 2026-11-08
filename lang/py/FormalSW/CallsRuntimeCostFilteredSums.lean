import lang.py.FormalSW.CallsRuntimeCostFunctions

/-! Filtered range sums charge every predicate, including rejected elements.
Bounds on selected values let a caller bound later work on the returned sum. -/
namespace FormalSW.PyAst.Calls.Runtime

theorem EvaluatesIn.boolean_single (op : BoolOp)
    (evaluated : EvaluatesIn arithmetic module env expression cost value) :
    EvaluatesIn arithmetic module env (.boolOp op [expression]) (cost + 2) value := by
  intro stack
  have finish : step module ⟨.value value, .boolean op [] env :: stack⟩ =
      .next ⟨.value value, stack⟩ := by
    dsimp only [step]
    simp only [ite_self]
    rfl
  have run := RuntimeCost.Reaches.next (charge := charge arithmetic module) (step := step module)
    (state := ⟨.expr (.boolOp op [expression]) env, stack⟩) rfl rfl
    ((evaluated _).trans (.next finish rfl .refl))
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem rangeSumFilteredWithin (module : Module) (sum : RangeSum)
    (testBound itemBound : Nat) (maxItem lower : Int) (nonnegative : 0 ≤ maxItem)
    (stride : sum.stride = 1)
    (tested : ∀ i, lower ≤ i → i < sum.stop → ∃ cost flag, cost ≤ testBound ∧
      EvaluatesIn .word module (sum.env.set sum.name (.int i)) sum.filter cost (.bool flag))
    (evaluated : ∀ i, lower ≤ i → i < sum.stop → ∃ cost value,
      cost ≤ itemBound ∧ 0 ≤ value ∧ value ≤ maxItem ∧
      EvaluatesIn .word module (sum.env.set sum.name (.int i)) sum.element cost (.int value))
    (remaining : Nat) (start total : Int) (begins : lower ≤ start)
    (stop : sum.stop = start + remaining) :
    ∃ cost answer, 7 * remaining + 4 ≤ cost ∧
      cost ≤ (testBound + itemBound + 12) * remaining + 4 ∧
      total ≤ answer ∧ answer ≤ total + remaining * maxItem ∧
      ∀ stack, RuntimeCost.Reaches (step module) (charge .word module)
        ⟨.sumLoop sum start total, stack⟩ cost ⟨.value (.int answer), stack⟩ := by
  induction remaining generalizing start total with
  | zero =>
      refine ⟨4, total, by simp, by simp, by omega, by simp, ?_⟩
      intro stack
      exact .next (amount := 4) (cost := 0)
        (by simp [step, rangeContinues, stop, stride]) rfl .refl
  | succ remaining ih =>
      have inside : start < sum.stop := by simp [stop]; omega
      have continues : rangeContinues start sum.stop sum.stride = true := by
        simp [rangeContinues, stride, inside]
      have nextStop : sum.stop = (start + 1) + remaining := by simp_all; omega
      have first (stack : List Frame) : step module ⟨.sumLoop sum start total, stack⟩ =
          .next ⟨.expr sum.filter (sum.env.set sum.name (.int start)),
            .sumFilter sum start total :: stack⟩ := by simp [step, continues]
      obtain ⟨testCost, flag, testUpper, testRun⟩ := tested start begins inside
      cases flag with
      | false =>
          obtain ⟨tailCost, answer, tailLower, tailUpper, answerLower, answerUpper, tail⟩ :=
            ih (start + 1) total (by omega) nextStop
          refine ⟨testCost + tailCost + 7, answer, ?_, ?_, answerLower, ?_, ?_⟩
          · rw [Nat.mul_succ]; omega
          · rw [Nat.mul_succ]; omega
          · simp only [Int.natCast_succ, Int.add_mul, Int.one_mul]; omega
          · intro stack
            have rejected : step module ⟨.value (.bool false), .sumFilter sum start total :: stack⟩ =
                .next ⟨.sumLoop sum (start + 1) total, stack⟩ := by simp [step, scalarTruth, stride]
            have run := RuntimeCost.Reaches.next (charge := charge .word module) (first stack) rfl
              ((testRun _).trans (.next rejected rfl (tail stack)))
            simpa only [rangeWork, PrimitiveWork.integer, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run
      | true =>
          obtain ⟨itemCost, item, itemUpper, positive, bounded, itemRun⟩ := evaluated start begins inside
          obtain ⟨tailCost, answer, tailLower, tailUpper, answerLower, answerUpper, tail⟩ :=
            ih (start + 1) (total + item) (by omega) nextStop
          refine ⟨testCost + itemCost + tailCost + 12, answer, ?_, ?_, by omega, ?_, ?_⟩
          · rw [Nat.mul_succ]; omega
          · rw [Nat.mul_succ]; omega
          · simp only [Int.natCast_succ, Int.add_mul, Int.one_mul]; omega
          · intro stack
            have selected : step module ⟨.value (.bool true), .sumFilter sum start total :: stack⟩ =
                .next ⟨.expr sum.element (sum.env.set sum.name (.int start)),
                  .sumElement sum start total :: stack⟩ := rfl
            have added : step module ⟨.value (.int item), .sumElement sum start total :: stack⟩ =
                .next ⟨.sumLoop sum (start + 1) (total + item), stack⟩ := by
              simp [step, sumAdd, stride]
            have run := RuntimeCost.Reaches.next (charge := charge .word module) (first stack) rfl
              ((testRun _).trans (.next selected rfl ((itemRun _).trans (.next added rfl (tail stack)))))
            simpa only [rangeWork, PrimitiveWork.integer, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

end FormalSW.PyAst.Calls.Runtime
