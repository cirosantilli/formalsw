import lang.py.FormalSW.HeapRuntimeCostDictionaries

/-! Scalar-key dictionary assignment pays the existing map lookup and reference
write tariff, using the live table after all argument effects. -/
namespace FormalSW.PyAst.HeapCalls.Runtime
variable {globals : Mutable.Globals}
open PrimitiveWork

/-- Evaluate the RHS before the receiver and index, then insert or replace in
the current dictionary. Stored values may be scalars or references; dictionary
writes preserve the potential of the entire heap. -/
theorem BlockContinuesIn.dictionary_setItem
    (ordinary : ∀ a b c, index ≠ .slice a b c)
    (rhs : EvaluatesIn (globals := globals) arithmetic module env expression heap cr value afterRhs)
    (args : ArgumentsIn (globals := globals) arithmetic module env 0 [base, index] afterRhs ca
      [.ref address, .scalar key] afterArgs)
    (found : afterArgs[address]? = some (.dict entries)) :
    BlockContinuesIn (globals := globals) arithmetic module env [.assign [.subscript base index] expression] heap
      (cr + ca + mapLookup .collisionChain entries.length
        (MapWork.keyWork arithmetic entries key) + 5)
      env (afterArgs.set address (.dict (ScalarDict.insert entries key value))) := by
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
  have evaluated := Mutable.setItem_dictionary afterArgs address entries found key value
  have write : Reaches (globals := globals) arithmetic module anchors
      ⟨.operation (.setItem value) [.ref address, .scalar key],
        .discard following env :: stack, afterArgs⟩
      (mapLookup .collisionChain entries.length (MapWork.keyWork arithmetic entries key) + 2)
      ⟨.value (.scalar .none), .discard following env :: stack,
        afterArgs.set address (.dict (ScalarDict.insert entries key value))⟩ := by
    apply RuntimeCost.Amortized.Reaches.next
      (amount := mapLookup .collisionChain entries.length (MapWork.keyWork arithmetic entries key) + 2)
    · simp [step, result, run, primitive, evaluated]
    · cases value with
      | scalar scalar =>
          cases key <;> cases scalar <;>
            simp [charge, operation, BufferWork.operation, scalarNumber,
              MapWork.operation, MapWork.lookup, found, Nat.add_assoc]
      | ref reference =>
          simp [charge, operation, BufferWork.operation,
            MapWork.operation, MapWork.lookup, found, Nat.add_assoc]
    · have equal := heapPotential_set afterArgs address (.dict entries)
        (.dict (ScalarDict.insert entries key value)) found
      simpa only [potential, objectPotential, Nat.add_zero] using
        Nat.add_le_add_left (Nat.le_of_eq equal)
          (mapLookup .collisionChain entries.length (MapWork.keyWork arithmetic entries key) + 2)
  have finish : Reaches (globals := globals) arithmetic module anchors
      ⟨.value (.scalar .none), .discard following env :: stack,
        afterArgs.set address (.dict (ScalarDict.insert entries key value))⟩ 1
      ⟨.block following env, stack,
        afterArgs.set address (.dict (ScalarDict.insert entries key value))⟩ := advance rfl rfl rfl
  exact (((((first.trans (rhs anchors _)).trans ready).trans arguments).trans write).trans finish).mono (by omega)

end FormalSW.PyAst.HeapCalls.Runtime
