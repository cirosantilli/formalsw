import lang.py.FormalSW.HeapRuntimeCostSorting

namespace FormalSW.PyAst.HeapCalls.Runtime

theorem sequenceMembership_integers (needle : Int) (items : List Int) :
    sequenceMembership .word (.scalar (.int needle)) (items.map (fun n => .scalar (.int n))) =
      some (3*items.length+1) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      simp [sequenceMembership, elementComparison, PrimitiveWork.comparison,
        PrimitiveWork.scalarSize, PrimitiveWork.integer, ih]
      omega

/-- Both operands finish evaluating before the membership scan. -/
theorem EvaluatesIn.membership
    (arguments : ArgumentsIn arithmetic module env 0 [needle, container] heap budget [value, receiver] middle)
    (evaluated : HeapCalls.membership value receiver negated middle = some (.ok (.scalar (.bool answer)), middle))
    (priced : operation arithmetic middle (.membership negated) [value, receiver] = some work) :
    EvaluatesIn arithmetic module env (.membership needle container negated) heap (budget+work+2)
      (.scalar (.bool answer)) middle := by
  intro anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.expr (.membership needle container negated) env, stack, heap⟩ 1
      (argumentsState (.membership negated) env [] [needle, container] stack heap) := advance rfl rfl rfl
  have scanned : Reaches arithmetic module anchors
      ⟨.operation (.membership negated) [value, receiver], stack, middle⟩ (work+1)
      ⟨.value (.scalar (.bool answer)), stack, middle⟩ :=
    advance (by simp [step, primitive, result, run, evaluated]) (by simp [charge, priced]) rfl
  exact ((first.trans (arguments.reaches (.membership negated) anchors stack)).trans scanned).mono (by omega)

end FormalSW.PyAst.HeapCalls.Runtime
