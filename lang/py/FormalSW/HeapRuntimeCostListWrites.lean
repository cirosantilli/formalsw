import lang.py.FormalSW.HeapRuntimeCostBuffers

/-! List item assignment retains the array size and capacity potential. Index
normalization is charged by the selected arithmetic model; the stored value is
copied by reference, including when the receiver refers to itself. -/
namespace FormalSW.PyAst.HeapCalls.Runtime
variable {globals : Mutable.Globals}
open PrimitiveWork

theorem BlockContinuesIn.list_setItem
    (ordinary : ∀ a b c, index ≠ .slice a b c)
    (rhs : EvaluatesIn (globals := globals) arithmetic module env expression heap cr value afterRhs)
    (args : ArgumentsIn (globals := globals) arithmetic module env 0 [base, index] afterRhs ca
      [.ref address, .scalar (.int offset)] afterArgs)
    (found : afterArgs[address]? = some (.list items))
    (evaluated : Mutable.setItem (.ref address) (.scalar (.int offset)) value afterArgs =
      some (.ok (.scalar .none), afterArgs.set address (.list (items.set position value)))) :
    BlockContinuesIn (globals := globals) arithmetic module env [.assign [.subscript base index] expression] heap
      (cr + ca + integer arithmetic offset + integer arithmetic items.length + 5)
      env (afterArgs.set address (.list (items.set position value))) := by
  intro following anchors stack
  have first : Reaches (globals := globals) arithmetic module anchors
      ⟨.block ([.assign [.subscript base index] expression] ++ following) env, stack, heap⟩ 1
      ⟨.expr expression env, .assignItem base index following env :: stack, heap⟩ :=
    advance (by cases index <;> simp_all [step]) rfl rfl
  have ready : Reaches (globals := globals) arithmetic module anchors
      ⟨.value value, .assignItem base index following env :: stack, afterRhs⟩ 1
      (argumentsState (.setItem value) env [] [base, index]
        (.discard following env :: stack) afterRhs) := advance rfl rfl rfl
  have arguments := args.reaches (completed := []) (.setItem value) anchors
    (.discard following env :: stack)
  have write : Reaches (globals := globals) arithmetic module anchors
      ⟨.operation (.setItem value) [.ref address, .scalar (.int offset)],
        .discard following env :: stack, afterArgs⟩
      (integer arithmetic offset + integer arithmetic items.length + 2)
      ⟨.value (.scalar .none), .discard following env :: stack,
        afterArgs.set address (.list (items.set position value))⟩ := by
    apply RuntimeCost.Amortized.Reaches.next
      (amount := integer arithmetic offset + integer arithmetic items.length + 2)
    · simp [step, result, run, primitive, evaluated]
    · simp [charge, operation, found, scalarNumber, Nat.add_assoc]
    · have equal := heapPotential_set afterArgs address (.list items)
        (.list (items.set position value)) found
      simp only [objectPotential, List.length_set] at equal
      simp only [potential]
      omega
  have finish : Reaches (globals := globals) arithmetic module anchors
      ⟨.value (.scalar .none), .discard following env :: stack,
        afterArgs.set address (.list (items.set position value))⟩ 1
      ⟨.block following env, stack, afterArgs.set address (.list (items.set position value))⟩ :=
    advance rfl rfl rfl
  exact (((((first.trans (rhs anchors _)).trans ready).trans arguments).trans write).trans finish).mono (by omega)

end FormalSW.PyAst.HeapCalls.Runtime
