import lang.py.FormalSW.HeapRuntimeCostSequences

namespace FormalSW.PyAst.HeapCalls.Runtime.EvaluatesIn

/-- The right operand of a chained comparison is evaluated just once and is
retained for the next comparison. Short-circuited operands incur no work. -/
def ComparesIn (arithmetic : PrimitiveWork.Arithmetic) (module : Module) (env : Env)
    (left : Value) (op : CmpOp) (right : Expr) (rest : List (CmpOp × Expr))
    (heap : Heap) (budget : Nat) (answer : Value) (finalHeap : Heap) : Prop :=
  ∀ anchors stack, Reaches arithmetic module anchors
    ⟨.expr right env, .chainRight op left rest env :: stack, heap⟩ budget
    ⟨.value answer, stack, finalHeap⟩

namespace ComparesIn

theorem last (evaluated : EvaluatesIn arithmetic module env right heap cost value middle)
    (compared : HeapCalls.compare op left value middle = some (.ok (.scalar answer), middle))
    (priced : comparison arithmetic middle op left value = some work) :
    ComparesIn arithmetic module env left op right [] heap (cost + work + 2) (.scalar answer) middle := by
  intro anchors stack
  have comparisonRun : Reaches arithmetic module anchors
      ⟨.value value, .chainRight op left [] env :: stack, middle⟩ (work + 1)
      ⟨.value (.scalar answer), .chainResult value [] env :: stack, middle⟩ :=
    advance (by simp [step, result, run, compared]) (by simp [charge, priced]) rfl
  have finish : Reaches arithmetic module anchors
      ⟨.value (.scalar answer), .chainResult value [] env :: stack, middle⟩ 1
      ⟨.value (.scalar answer), stack, middle⟩ := advance rfl rfl rfl
  exact (((evaluated anchors _).trans comparisonRun).trans finish).mono (by omega)

theorem stop (evaluated : EvaluatesIn arithmetic module env right heap cost value middle)
    (compared : HeapCalls.compare op left value middle = some (.ok (.scalar answer), middle))
    (priced : comparison arithmetic middle op left value = some work)
    (test : Mutable.truth (.scalar answer) middle = some (.ok false, middle)) :
    ComparesIn arithmetic module env left op right (next :: rest) heap
      (cost + work + 2) (.scalar answer) middle := by
  intro anchors stack
  have comparisonRun : Reaches arithmetic module anchors
      ⟨.value value, .chainRight op left (next :: rest) env :: stack, middle⟩ (work + 1)
      ⟨.value (.scalar answer), .chainResult value (next :: rest) env :: stack, middle⟩ :=
    advance (by simp [step, result, run, compared]) (by simp [charge, priced]) rfl
  have finish : Reaches arithmetic module anchors
      ⟨.value (.scalar answer), .chainResult value (next :: rest) env :: stack, middle⟩ 1
      ⟨.value (.scalar answer), stack, middle⟩ := advance (by simp [step, run, test]) rfl rfl
  exact (((evaluated anchors _).trans comparisonRun).trans finish).mono (by omega)

theorem next (evaluated : EvaluatesIn arithmetic module env right heap ca value middle)
    (compared : HeapCalls.compare op left value middle = some (.ok (.scalar comparisonResult), middle))
    (priced : comparison arithmetic middle op left value = some work)
    (test : Mutable.truth (.scalar comparisonResult) middle = some (.ok true, middle))
    (following : ComparesIn arithmetic module env value nextOp nextRight rest middle cb answer finalHeap) :
    ComparesIn arithmetic module env left op right ((nextOp, nextRight) :: rest) heap
      (ca + cb + work + 2) answer finalHeap := by
  intro anchors stack
  have comparisonRun : Reaches arithmetic module anchors
      ⟨.value value, .chainRight op left ((nextOp, nextRight) :: rest) env :: stack, middle⟩ (work + 1)
      ⟨.value (.scalar comparisonResult), .chainResult value ((nextOp, nextRight) :: rest) env :: stack, middle⟩ :=
    advance (by simp [step, HeapCalls.result, run, compared]) (by simp [charge, priced]) rfl
  have resume : Reaches arithmetic module anchors
      ⟨.value (.scalar comparisonResult), .chainResult value ((nextOp, nextRight) :: rest) env :: stack, middle⟩ 1
      ⟨.expr nextRight env, .chainRight nextOp value rest env :: stack, middle⟩ :=
    advance (by simp [step, run, test]) rfl rfl
  exact ((((evaluated anchors _).trans comparisonRun).trans resume).trans (following anchors stack)).mono (by omega)

end ComparesIn

theorem chain (left : EvaluatesIn arithmetic module env expression heap ca value middle)
    (following : ComparesIn arithmetic module env value op right (next :: rest) middle cb answer finalHeap) :
    EvaluatesIn arithmetic module env (.compare expression ((op, right) :: next :: rest)) heap
      (ca + cb + 2) answer finalHeap := by
  intro anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.expr (.compare expression ((op, right) :: next :: rest)) env, stack, heap⟩ 1
      ⟨.expr expression env, .chainLeft op right (next :: rest) env :: stack, heap⟩ := advance rfl rfl rfl
  have ready : Reaches arithmetic module anchors
      ⟨.value value, .chainLeft op right (next :: rest) env :: stack, middle⟩ 1
      ⟨.expr right env, .chainRight op value (next :: rest) env :: stack, middle⟩ := advance rfl rfl rfl
  exact (((first.trans (left anchors _)).trans ready).trans (following anchors stack)).mono (by omega)

end FormalSW.PyAst.HeapCalls.Runtime.EvaluatesIn
