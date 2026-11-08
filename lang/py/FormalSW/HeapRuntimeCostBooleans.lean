import lang.py.FormalSW.HeapRuntimeCostSequences

namespace FormalSW.PyAst.HeapCalls.Runtime.EvaluatesIn

theorem boolean_last (evaluated : EvaluatesIn arithmetic module env expression heap cost (.scalar value) middle)
    (test : Mutable.truth (.scalar value) middle = some (.ok flag, middle)) :
    EvaluatesIn arithmetic module env (.boolOp op [expression]) heap (cost + 2) (.scalar value) middle := by
  intro anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.expr (.boolOp op [expression]) env, stack, heap⟩ 1
      ⟨.expr expression env, .boolean op [] env :: stack, heap⟩ := advance rfl rfl rfl
  have last : Reaches arithmetic module anchors
      ⟨.value (.scalar value), .boolean op [] env :: stack, middle⟩ 1
      ⟨.value (.scalar value), stack, middle⟩ :=
    advance (by cases op <;> cases flag <;> simp [step, run, test]) rfl rfl
  exact ((first.trans (evaluated anchors _)).trans last).mono (by omega)

/-- Reuse the continuation of the remaining Boolean operands. Its budget may
retain the saved expression-entry unit, giving a conservative compositional rule. -/
theorem boolean_next (evaluated : EvaluatesIn arithmetic module env first heap ca (.scalar value) middle)
    (test : Mutable.truth (.scalar value) middle = some (.ok flag, middle))
    (continues : (match op with | .and => !flag | .or => flag) = false)
    (rest : EvaluatesIn arithmetic module env (.boolOp op (next :: tail)) middle cb answer finalHeap) :
    EvaluatesIn arithmetic module env (.boolOp op (first :: next :: tail)) heap (ca + cb + 2) answer finalHeap := by
  intro anchors stack
  have start : Reaches arithmetic module anchors
      ⟨.expr (.boolOp op (first :: next :: tail)) env, stack, heap⟩ 1
      ⟨.expr first env, .boolean op (next :: tail) env :: stack, heap⟩ := advance rfl rfl rfl
  have resume : Reaches arithmetic module anchors
      ⟨.value (.scalar value), .boolean op (next :: tail) env :: stack, middle⟩ 1
      ⟨.expr next env, .boolean op tail env :: stack, middle⟩ :=
    advance (by cases op <;> cases flag <;> simp_all [step, run]) rfl rfl
  obtain ⟨actual, trace, paid⟩ := rest anchors stack
  cases trace with
  | next transition measured following =>
      simp only [step, protectGenerator_next, Step.next.injEq] at transition
      subst transition
      have remaining : Reaches arithmetic module anchors
          ⟨.expr next env, .boolean op tail env :: stack, middle⟩ cb
          ⟨.value answer, stack, finalHeap⟩ := by
        refine ⟨_, following, ?_⟩
        simp only [potential] at paid ⊢
        omega
      exact (((start.trans (evaluated anchors _)).trans resume).trans remaining).mono (by omega)

end FormalSW.PyAst.HeapCalls.Runtime.EvaluatesIn
