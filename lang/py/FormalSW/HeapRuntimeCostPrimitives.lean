import lang.py.FormalSW.HeapRuntimeCostBufferLoops
import lang.py.FormalSW.HeapRuntimeCostReturns

namespace FormalSW.PyAst.HeapCalls.Runtime
variable {globals : Mutable.Globals}

theorem EvaluatesIn.builtin_single
    (notAll : builtin ≠ .all) (notAny : builtin ≠ .any)
    (argument : EvaluatesIn (globals := globals) arithmetic module env expression heap ca value middle)
    (evaluated : primitive (.builtin builtin) [value] middle = some (.ok answer, middle))
    (priced : operation arithmetic middle (.builtin builtin) [value] = some work) :
    EvaluatesIn (globals := globals) arithmetic module env (.builtinCall builtin [expression]) heap
      (ca + work + 3) answer middle := by
  intro anchors stack
  have first : Reaches (globals := globals) arithmetic module anchors
      ⟨.expr (.builtinCall builtin [expression]) env, stack, heap⟩ 1
      ⟨.expr expression env, .arguments (.builtin builtin) [] [] env :: stack, heap⟩ := advance rfl rfl rfl
  have ready : Reaches (globals := globals) arithmetic module anchors
      ⟨.value value, .arguments (.builtin builtin) [] [] env :: stack, middle⟩ 1
      ⟨.operation (.builtin builtin) [value], stack, middle⟩ := advance rfl rfl rfl
  have last : Reaches (globals := globals) arithmetic module anchors
      ⟨.operation (.builtin builtin) [value], stack, middle⟩ (work+1)
      ⟨.value answer, stack, middle⟩ :=
    advance (by cases builtin <;> first | contradiction | simp only [step, result, run, evaluated, protectGenerator_next])
      (by simp [charge, priced]) rfl
  exact (((first.trans (argument anchors _)).trans ready).trans last).mono (by omega)

theorem BlockContinuesIn.buffer_setItem
    (ordinary : ∀ a b c, index ≠ .slice a b c)
    (rhs : EvaluatesIn (globals := globals) arithmetic module env expression heap cr (.scalar (.int value)) afterRhs)
    (args : ArgumentsIn (globals := globals) arithmetic module env 0 [base, index] afterRhs ca
      [.ref address, .scalar (.int offset)] afterArgs)
    (found : afterArgs[address]? = some (.bytearray bytes))
    (evaluated : Mutable.setItem (.ref address) (.scalar (.int offset)) (.scalar (.int value)) afterArgs =
      some (.ok (.scalar .none), afterArgs.set address (.bytearray updated))) :
    BlockContinuesIn (globals := globals) arithmetic module env [.assign [.subscript base index] expression] heap
      (cr + ca + PrimitiveWork.integer arithmetic offset + PrimitiveWork.integer arithmetic bytes.length +
        PrimitiveWork.integer arithmetic value + 5) env (afterArgs.set address (.bytearray updated)) := by
  intro following anchors stack
  have first : Reaches (globals := globals) arithmetic module anchors
      ⟨.block ([.assign [.subscript base index] expression] ++ following) env, stack, heap⟩ 1
      ⟨.expr expression env, .assignItem base index following env :: stack, heap⟩ :=
    advance (by cases index <;> simp_all [step]) rfl rfl
  have ready : Reaches (globals := globals) arithmetic module anchors
      ⟨.value (.scalar (.int value)), .assignItem base index following env :: stack, afterRhs⟩ 1
      (argumentsState (.setItem (.scalar (.int value))) env [] [base, index]
        (.discard following env :: stack) afterRhs) := advance rfl rfl rfl
  have arguments := args.reaches (completed := []) (.setItem (.scalar (.int value))) anchors
    (.discard following env :: stack)
  have write : Reaches (globals := globals) arithmetic module anchors
      ⟨.operation (.setItem (.scalar (.int value))) [.ref address, .scalar (.int offset)],
        .discard following env :: stack, afterArgs⟩
      (PrimitiveWork.integer arithmetic offset + PrimitiveWork.integer arithmetic bytes.length +
        PrimitiveWork.integer arithmetic value + 2)
      ⟨.value (.scalar .none), .discard following env :: stack, afterArgs.set address (.bytearray updated)⟩ := by
    apply RuntimeCost.Amortized.Reaches.next
      (amount := PrimitiveWork.integer arithmetic offset + PrimitiveWork.integer arithmetic bytes.length +
        PrimitiveWork.integer arithmetic value + 2)
    · simp [step, result, run, primitive, evaluated]
    · simp [charge, operation, BufferWork.operation, found, scalarNumber, Nat.add_assoc]
    · have equal := heapPotential_set afterArgs address (.bytearray bytes) (.bytearray updated) found
      simpa only [potential, objectPotential, Nat.add_zero] using
        Nat.add_le_add_left (Nat.le_of_eq equal)
          (PrimitiveWork.integer arithmetic offset + PrimitiveWork.integer arithmetic bytes.length +
            PrimitiveWork.integer arithmetic value + 2)
  have finish : Reaches (globals := globals) arithmetic module anchors
      ⟨.value (.scalar .none), .discard following env :: stack, afterArgs.set address (.bytearray updated)⟩ 1
      ⟨.block following env, stack, afterArgs.set address (.bytearray updated)⟩ := advance rfl rfl rfl
  exact (((((first.trans (rhs anchors _)).trans ready).trans arguments).trans write).trans finish).mono (by omega)

theorem BlockReturnsIn.assertion
    (evaluated : EvaluatesIn (globals := globals) arithmetic module env condition heap ca (.scalar (.bool true)) middle)
    (rest : BlockReturnsIn (globals := globals) arithmetic module env following middle cb answer finalHeap) :
    BlockReturnsIn (globals := globals) arithmetic module env (.assert condition message :: following) heap
      (ca+cb+2) answer finalHeap := by
  intro anchors stack
  have first : Reaches (globals := globals) arithmetic module anchors
      ⟨.block (.assert condition message :: following) env, stack, heap⟩ 1
      ⟨.expr condition env, .assertion message following env :: stack, heap⟩ := advance rfl rfl rfl
  have next : Reaches (globals := globals) arithmetic module anchors
      ⟨.value (.scalar (.bool true)), .assertion message following env :: stack, middle⟩ 1
      ⟨.block following env, stack, middle⟩ := advance rfl rfl rfl
  exact (((first.trans (evaluated anchors _)).trans next).trans (rest anchors stack)).mono (by omega)

end FormalSW.PyAst.HeapCalls.Runtime
