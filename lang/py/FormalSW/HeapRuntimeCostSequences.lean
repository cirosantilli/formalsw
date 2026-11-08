import lang.py.FormalSW.HeapRuntimeCostPrimitives

/-! Indexed sequence reads and short-circuit scans. Index arithmetic follows
 the selected model; array access copies a pointer, not its referenced object. -/
namespace FormalSW.PyAst.HeapCalls.Runtime
open PrimitiveWork

namespace EvaluatesIn

theorem list_subscript (ordinary : ∀ a b c, index ≠ .slice a b c)
    (receiver : EvaluatesIn arithmetic module env base heap ca (.ref address) middle)
    (position : EvaluatesIn arithmetic module env index middle cb (.scalar (.int offset)) afterIndex)
    (found : afterIndex[address]? = some (.list items))
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

theorem boolean_stop (evaluated : EvaluatesIn arithmetic module env first heap cost (.scalar value) middle)
    (truth : Mutable.truth (.scalar value) middle = some (.ok flag, middle))
    (stop : (match op with | .and => !flag | .or => flag) = true) :
    EvaluatesIn arithmetic module env (.boolOp op (first :: rest)) heap (cost + 2) (.scalar value) middle := by
  intro anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.expr (.boolOp op (first :: rest)) env, stack, heap⟩ 1
      ⟨.expr first env, .boolean op rest env :: stack, heap⟩ := advance rfl rfl rfl
  have last : Reaches arithmetic module anchors
      ⟨.value (.scalar value), .boolean op rest env :: stack, middle⟩ 1
      ⟨.value (.scalar value), stack, middle⟩ :=
    advance (by cases op <;> cases flag <;> simp_all [step, run]) rfl rfl
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (initial.trans (evaluated anchors _)).trans last

theorem boolean_pair (left : EvaluatesIn arithmetic module env first heap ca (.scalar value) middle)
    (truth : Mutable.truth (.scalar value) middle = some (.ok flag, middle))
    (continues : (match op with | .and => !flag | .or => flag) = false)
    (right : EvaluatesIn arithmetic module env second middle cb (.scalar answer) finalHeap)
    (answerTruth : Mutable.truth (.scalar answer) finalHeap = some (.ok answerFlag, finalHeap)) :
    EvaluatesIn arithmetic module env (.boolOp op [first, second]) heap (ca + cb + 3) (.scalar answer) finalHeap := by
  intro anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.expr (.boolOp op [first, second]) env, stack, heap⟩ 1
      ⟨.expr first env, .boolean op [second] env :: stack, heap⟩ := advance rfl rfl rfl
  have next : Reaches arithmetic module anchors
      ⟨.value (.scalar value), .boolean op [second] env :: stack, middle⟩ 1
      ⟨.expr second env, .boolean op [] env :: stack, middle⟩ :=
    advance (by cases op <;> cases flag <;> simp_all [step, run]) rfl rfl
  have last : Reaches arithmetic module anchors
      ⟨.value (.scalar answer), .boolean op [] env :: stack, finalHeap⟩ 1
      ⟨.value (.scalar answer), stack, finalHeap⟩ :=
    advance (by cases op <;> cases answerFlag <;> simp [step, run, answerTruth]) rfl rfl
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (((initial.trans (left anchors _)).trans next).trans (right anchors _)).trans last

end EvaluatesIn

namespace BlockContinuesIn

theorem while_loop (evaluated : EvaluatesIn arithmetic module env condition heap cc (.scalar value) middle)
    (truth : Mutable.truth (.scalar value) middle = some (.ok flag, middle))
    (rest : BlockContinuesIn arithmetic module env
      (if flag then body ++ [Calls.loopContinuation body (.whileDo condition body otherwise)] else otherwise)
      middle cb finalEnv finalHeap) :
    BlockContinuesIn arithmetic module env [.whileDo condition body otherwise] heap (cc + cb + 2) finalEnv finalHeap := by
  intro following anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.block ([.whileDo condition body otherwise] ++ following) env, stack, heap⟩ 1
      ⟨.expr condition env, .branch (body ++ [Calls.loopContinuation body (.whileDo condition body otherwise)])
        otherwise following env :: stack, heap⟩ := advance rfl rfl rfl
  have next : Reaches arithmetic module anchors
      ⟨.value (.scalar value), .branch (body ++ [Calls.loopContinuation body (.whileDo condition body otherwise)])
        otherwise following env :: stack, middle⟩ 1
      ⟨.block ((if flag then body ++ [Calls.loopContinuation body (.whileDo condition body otherwise)] else otherwise) ++ following)
        env, stack, middle⟩ := advance (by simp [step, run, truth]) rfl rfl
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    ((initial.trans (evaluated anchors _)).trans next).trans (rest following anchors stack)

end BlockContinuesIn
end FormalSW.PyAst.HeapCalls.Runtime
