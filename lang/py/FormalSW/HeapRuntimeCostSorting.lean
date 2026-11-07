import lang.py.FormalSW.HeapRuntimeCostListCopies

namespace FormalSW.PyAst.HeapCalls.Runtime
open PrimitiveWork

theorem EvaluatesIn.tuple
    (arguments : ArgumentsIn arithmetic module env 0 expressions heap budget items middle)
    (nonempty : items ≠ []) :
    EvaluatesIn arithmetic module env (.tuple expressions) heap (budget + items.length + 3)
      (.ref middle.length) (middle ++ [.tuple items]) := by
  intro anchors stack
  have first : Reaches arithmetic module anchors ⟨.expr (.tuple expressions) env, stack, heap⟩ 1
      (argumentsState .tuple env [] expressions stack heap) := advance rfl rfl (by cases expressions <;> rfl)
  have allocated : Reaches arithmetic module anchors
      ⟨.operation .tuple items, stack, middle⟩ (items.length + 2)
      ⟨.value (.ref middle.length), stack, middle ++ [.tuple items]⟩ := by
    apply RuntimeCost.Amortized.Reaches.next (amount := items.length + 2)
    · simp [step, primitive, result, run, Mutable.allocateTuple, nonempty, Except.map]
    · rfl
    · simp [potential, heapPotential, objectPotential]
  exact ((first.trans (arguments.reaches .tuple anchors stack)).trans allocated).mono (by omega)

theorem EvaluatesIn.tuple_subscript (ordinary : ∀ a b c, index ≠ .slice a b c)
    (receiver : EvaluatesIn arithmetic module env base heap ca (.ref address) middle)
    (position : EvaluatesIn arithmetic module env index middle cb (.scalar (.int offset)) afterIndex)
    (found : afterIndex[address]? = some (.tuple items))
    (evaluated : Mutable.getItem (.ref address) (.scalar (.int offset)) afterIndex =
      some (.ok answer, afterIndex)) :
    EvaluatesIn arithmetic module env (.subscript base index) heap
      (ca + cb + integer arithmetic offset + integer arithmetic items.length + 6) answer afterIndex := by
  intro anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.expr (.subscript base index) env, stack, heap⟩ 1
      (argumentsState .subscript env [] [base, index] stack heap) :=
    advance (by cases index <;> simp_all [step, argumentsState]) rfl rfl
  have args := (ArgumentsIn.cons receiver (ArgumentsIn.cons position ArgumentsIn.nil)).reaches
    (completed := []) .subscript anchors stack
  have last : Reaches arithmetic module anchors
      ⟨.operation .subscript [.ref address, .scalar (.int offset)], stack, afterIndex⟩
      (integer arithmetic offset + integer arithmetic items.length + 2)
      ⟨.value answer, stack, afterIndex⟩ :=
    advance (by simp [step, primitive, result, run, evaluated])
      (by simp [charge, operation, scalarNumber, found]) rfl
  exact ((initial.trans args).trans last).mono (by simp; omega)

theorem EvaluatesIn.sorted
    (argument : EvaluatesIn arithmetic module env expression heap ca source middle)
    (evaluated : primitive (.builtin .sorted) [source] middle =
      some (.ok (.ref middle.length), middle ++ [.list output]))
    (priced : operation arithmetic middle (.builtin .sorted) [source] = some work) :
    EvaluatesIn arithmetic module env (.builtinCall .sorted [expression]) heap
      (ca + work + output.length + 3) (.ref middle.length) (middle ++ [.list output]) := by
  intro anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.expr (.builtinCall .sorted [expression]) env, stack, heap⟩ 1
      ⟨.expr expression env, .arguments (.builtin .sorted) [] [] env :: stack, heap⟩ := advance rfl rfl rfl
  have ready : Reaches arithmetic module anchors
      ⟨.value source, .arguments (.builtin .sorted) [] [] env :: stack, middle⟩ 1
      ⟨.operation (.builtin .sorted) [source], stack, middle⟩ := advance rfl rfl rfl
  have ordered : Reaches arithmetic module anchors
      ⟨.operation (.builtin .sorted) [source], stack, middle⟩ (work + output.length + 1)
      ⟨.value (.ref middle.length), stack, middle ++ [.list output]⟩ := by
    apply RuntimeCost.Amortized.Reaches.next (amount := work + 1)
    · simp [step, result, run, evaluated]
    · simp [charge, priced]
    · have credits := DynamicArray.potential_le output.length
      simp only [potential, heapPotential_allocate]
      omega
  exact (((first.trans (argument anchors _)).trans ready).trans ordered).mono (by omega)

theorem BlockContinuesIn.unpack_list
    (targetsValid : Calls.targetNames targets = some names)
    (evaluated : EvaluatesIn arithmetic module env expression heap cost (.ref address) middle)
    (found : middle[address]? = some (.list items)) (arity : names.length = items.length) :
    BlockContinuesIn arithmetic module env [.assign [.tuple targets] expression] heap
      (cost + targets.length + items.length + names.length + 2)
      (assignNames env names items) middle := by
  intro following anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.block ([.assign [.tuple targets] expression] ++ following) env, stack, heap⟩ (targets.length + 1)
      ⟨.expr expression env, .unpack names following env :: stack, heap⟩ :=
    advance (by simp [step, targetsValid]) (by simp [charge, targetsValid]) rfl
  have assigned : Reaches arithmetic module anchors
      ⟨.value (.ref address), .unpack names following env :: stack, middle⟩ (items.length + names.length + 1)
      ⟨.block following (assignNames env names items), stack, middle⟩ :=
    advance (by simp [step, run, Mutable.sequence, found, arity])
      (by simp [charge, sequenceLength, found]) rfl
  exact ((first.trans (evaluated anchors _)).trans assigned).mono (by omega)

end FormalSW.PyAst.HeapCalls.Runtime
