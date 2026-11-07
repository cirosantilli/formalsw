import lang.py.FormalSW.HeapRuntimeCostListWrites

/-! Indexed augmented assignment saves the receiver, index and old scalar before
the RHS. Its read and write each pay for signed-index normalization. RHS effects
may change the list, so the write uses its live length and contents. -/
namespace FormalSW.PyAst.HeapCalls.Runtime
variable {globals : Mutable.Globals}
open PrimitiveWork

/-- Compose the actual `base[index] op= expression` execution. Receiver and index
expressions may have effects, and the RHS may mutate the same list through an
alias. Only the scalar in-place operation itself must preserve the heap. -/
theorem BlockContinuesIn.list_augAssignItem
    (ordinary : ∀ a b c, index ≠ .slice a b c)
    (receiver : EvaluatesIn (globals := globals) arithmetic module env base heap cb
      (.ref address) afterReceiver)
    (subscript : EvaluatesIn (globals := globals) arithmetic module env index afterReceiver ci
      (.scalar (.int offset)) afterIndex)
    (before : afterIndex[address]? = some (.list items))
    (read : Mutable.getItem (.ref address) (.scalar (.int offset)) afterIndex =
      some (.ok (.scalar left), afterIndex))
    (rhs : EvaluatesIn (globals := globals) arithmetic module env expression afterIndex cr
      (.scalar right) afterRhs)
    (evaluated : inplace op (.scalar left) (.scalar right) afterRhs =
      some (.ok updated, afterRhs))
    (priced : PrimitiveWork.binary arithmetic op left right = some work)
    (live : afterRhs[address]? = some (.list current))
    (written : Mutable.setItem (.ref address) (.scalar (.int offset)) updated afterRhs =
      some (.ok (.scalar .none), afterRhs.set address (.list (current.set position updated)))) :
    BlockContinuesIn (globals := globals) arithmetic module env
      [.augAssign (.subscript base index) op expression] heap
      (cb + ci + cr + 2 * integer arithmetic offset + integer arithmetic items.length +
        integer arithmetic current.length + work + 8)
      env (afterRhs.set address (.list (current.set position updated))) := by
  intro following anchors stack
  have first : Reaches (globals := globals) arithmetic module anchors
      ⟨.block ([.augAssign (.subscript base index) op expression] ++ following) env, stack, heap⟩ 1
      ⟨.expr base env, .augmentItemReceiver index op expression following env :: stack, heap⟩ :=
    advance (by cases index <;> simp_all [step])
      (by cases index <;> simp_all [charge]) rfl
  have ready : Reaches (globals := globals) arithmetic module anchors
      ⟨.value (.ref address), .augmentItemReceiver index op expression following env :: stack, afterReceiver⟩ 1
      ⟨.expr index env, .augmentItemIndex (.ref address) op expression following env :: stack, afterReceiver⟩ :=
    advance rfl rfl rfl
  have loaded : Reaches (globals := globals) arithmetic module anchors
      ⟨.value (.scalar (.int offset)),
        .augmentItemIndex (.ref address) op expression following env :: stack, afterIndex⟩
      (integer arithmetic offset + integer arithmetic items.length + 2)
      ⟨.expr expression env, .binaryRight op (.scalar left) true ::
        .writeItem (.ref address) (.scalar (.int offset)) following env :: stack, afterIndex⟩ :=
    advance (by simp [step, run, read])
      (by simp [charge, operation, before, scalarNumber, Nat.add_assoc]) rfl
  have calculated : Reaches (globals := globals) arithmetic module anchors
      ⟨.value (.scalar right), .binaryRight op (.scalar left) true ::
        .writeItem (.ref address) (.scalar (.int offset)) following env :: stack, afterRhs⟩
      (work + 1)
      ⟨.value updated, .writeItem (.ref address) (.scalar (.int offset)) following env :: stack, afterRhs⟩ :=
    advance (by simp [step, result, run, evaluated]) (by simp [charge, priced]) rfl
  have write : Reaches (globals := globals) arithmetic module anchors
      ⟨.value updated, .writeItem (.ref address) (.scalar (.int offset)) following env :: stack, afterRhs⟩
      (integer arithmetic offset + integer arithmetic current.length + 2)
      ⟨.value (.scalar .none), .discard following env :: stack,
        afterRhs.set address (.list (current.set position updated))⟩ := by
    apply RuntimeCost.Amortized.Reaches.next
      (amount := integer arithmetic offset + integer arithmetic current.length + 2)
    · simp [step, result, run, written]
    · simp [charge, operation, live, scalarNumber, Nat.add_assoc]
    · have equal := heapPotential_set afterRhs address (.list current)
        (.list (current.set position updated)) live
      simp only [objectPotential, List.length_set] at equal
      simp only [potential]
      omega
  have finish : Reaches (globals := globals) arithmetic module anchors
      ⟨.value (.scalar .none), .discard following env :: stack,
        afterRhs.set address (.list (current.set position updated))⟩ 1
      ⟨.block following env, stack, afterRhs.set address (.list (current.set position updated))⟩ :=
    advance rfl rfl rfl
  exact ((((((((first.trans (receiver anchors _)).trans ready).trans (subscript anchors _)).trans
    loaded).trans (rhs anchors _)).trans calculated).trans write).trans finish).mono (by omega)

end FormalSW.PyAst.HeapCalls.Runtime
