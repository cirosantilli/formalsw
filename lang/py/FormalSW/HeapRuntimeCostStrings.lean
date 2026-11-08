import lang.py.FormalSW.HeapRuntimeCostSequences

/-! Scalar string and bytes access in the heap interpreter uses the same tariffs
as the scalar interpreter. Slices pay for copying; argument evaluation may
change the heap even though the final scalar operation does not. -/
namespace FormalSW.PyAst.HeapCalls.Runtime.EvaluatesIn

theorem scalar_slice
    (arguments : ArgumentsIn arithmetic module env 0
      [base, lower.getD (.constant .none), upper.getD (.constant .none), stride.getD (.constant .none)]
      heap budget [.scalar receiver, .scalar first, .scalar last, .scalar stepValue] middle)
    (evaluated : Mutable.getSlice (.scalar receiver) (.scalar first) (.scalar last) (.scalar stepValue) middle =
      some (.ok (.scalar answer), middle))
    (priced : Calls.Runtime.primitive arithmetic .slice [receiver, first, last, stepValue] = some work) :
    EvaluatesIn arithmetic module env (.subscript base (.slice lower upper stride)) heap
      (budget + work + 2) (.scalar answer) middle := by
  intro anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.expr (.subscript base (.slice lower upper stride)) env, stack, heap⟩ 1
      (argumentsState .slice env [] [base, lower.getD (.constant .none),
        upper.getD (.constant .none), stride.getD (.constant .none)] stack heap) := advance rfl rfl rfl
  have sliced : Reaches arithmetic module anchors
      ⟨.operation .slice [.scalar receiver, .scalar first, .scalar last, .scalar stepValue], stack, middle⟩
      (work+1) ⟨.value (.scalar answer), stack, middle⟩ :=
    advance (by simp [step, result, run, primitive, evaluated])
      (by simp [charge, operation, priced]) rfl
  exact ((initial.trans (arguments.reaches .slice anchors stack)).trans sliced).mono (by omega)

theorem scalar_subscript (ordinary : ∀ a b c, index ≠ .slice a b c)
    (receiver : EvaluatesIn arithmetic module env base heap ca (.scalar value) middle)
    (position : EvaluatesIn arithmetic module env index middle cb (.scalar offset) afterIndex)
    (evaluated : Mutable.getItem (.scalar value) (.scalar offset) afterIndex =
      some (.ok (.scalar answer), afterIndex))
    (priced : Calls.Runtime.primitive arithmetic .subscript [value, offset] = some work) :
    EvaluatesIn arithmetic module env (.subscript base index) heap
      (ca + cb + work + 5) (.scalar answer) afterIndex := by
  intro anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.expr (.subscript base index) env, stack, heap⟩ 1
      (argumentsState .subscript env [] [base, index] stack heap) :=
    advance (by cases index <;> simp_all [step, argumentsState]) rfl rfl
  have args := (ArgumentsIn.cons receiver (ArgumentsIn.cons position ArgumentsIn.nil)).reaches
    (completed := []) .subscript anchors stack
  have read : Reaches arithmetic module anchors
      ⟨.operation .subscript [.scalar value, .scalar offset], stack, afterIndex⟩ (work+1)
      ⟨.value (.scalar answer), stack, afterIndex⟩ :=
    advance (by simp [step, result, run, primitive, evaluated])
      (by simp [charge, operation, priced]) rfl
  exact ((initial.trans args).trans read).mono (by simp; omega)

end FormalSW.PyAst.HeapCalls.Runtime.EvaluatesIn
