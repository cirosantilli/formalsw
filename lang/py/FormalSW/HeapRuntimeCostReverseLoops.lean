import lang.py.FormalSW.HeapRuntimeCostControl

/-! A reverse list iterator retains the original receiver and reads its current
contents. It allocates no reversed copy and charges its private index arithmetic. -/
namespace FormalSW.PyAst.HeapCalls.Runtime.BlockContinuesIn
variable {globals : Mutable.Globals}
open PrimitiveWork

theorem for_reversed_list
    (evaluated : EvaluatesIn (globals := globals) arithmetic module env iterable heap cost (.ref address) middle)
    (found : middle[address]? = some (.list items))
    (rest : BlockContinuesIn (globals := globals) arithmetic module env
      [.reverseSequenceStepLoop name (.ref address) ((items.length : Int) - 1) body otherwise]
      middle budget finalEnv finalHeap) :
    BlockContinuesIn (globals := globals) arithmetic module env [.forReversed name iterable body otherwise]
      heap (cost + budget + integer arithmetic items.length + 3) finalEnv finalHeap := by
  intro following anchors stack
  have first : Reaches (globals := globals) arithmetic module anchors
      ⟨.block ([.forReversed name iterable body otherwise] ++ following) env, stack, heap⟩ 1
      ⟨.expr iterable env, .reverseSequence name body otherwise following env :: stack, heap⟩ :=
    advance rfl rfl rfl
  have start : Reaches (globals := globals) arithmetic module anchors
      ⟨.value (.ref address), .reverseSequence name body otherwise following env :: stack, middle⟩
      (2 + integer arithmetic items.length)
      ⟨.block (.reverseSequenceStepLoop name (.ref address) ((items.length : Int) - 1) body otherwise :: following)
        env, stack, middle⟩ :=
    advance (by simp [step, run, Mutable.reversibleSequence, Mutable.sequence, found, sequenceSource])
      (by simp [charge, found]) rfl
  exact (((first.trans (evaluated anchors _)).trans start).trans (rest following anchors stack)).mono (by omega)

theorem reverse_list_step (nonnegative : 0 ≤ position)
    (found : heap[address]? = some (.list items)) (item : items[position.toNat]? = some value)
    (rest : BlockContinuesIn (globals := globals) arithmetic module (setLocal env name value)
      (body ++ [Calls.loopContinuation body (.reverseSequenceStepLoop name (.ref address) (position - 1) body otherwise)])
      heap budget finalEnv finalHeap) :
    BlockContinuesIn (globals := globals) arithmetic module env
      [.reverseSequenceStepLoop name (.ref address) position body otherwise]
      heap (budget + 2 + 2 * integer arithmetic position + integer arithmetic items.length) finalEnv finalHeap := by
  intro following anchors stack
  have first : Reaches (globals := globals) arithmetic module anchors
      ⟨.block ([.reverseSequenceStepLoop name (.ref address) position body otherwise] ++ following) env, stack, heap⟩
      (2 + 2 * integer arithmetic position + integer arithmetic items.length)
      ⟨.block ((body ++ [Calls.loopContinuation body
          (.reverseSequenceStepLoop name (.ref address) (position - 1) body otherwise)]) ++ following)
        (setLocal env name value), stack, heap⟩ :=
    advance (by simp [step, run, Mutable.reversibleSequence, Mutable.sequence, sequenceValue,
        found, Int.not_lt.mpr nonnegative, item, List.append_assoc])
      (by simp [charge, Int.not_lt.mpr nonnegative, found]) rfl
  exact (first.trans (rest following anchors stack)).mono (by omega)

theorem reverse_done (finished : position < 0)
    (rest : BlockContinuesIn (globals := globals) arithmetic module env otherwise heap budget finalEnv finalHeap) :
    BlockContinuesIn (globals := globals) arithmetic module env [.reverseSequenceStepLoop name source position body otherwise]
      heap (budget + 1 + integer arithmetic position) finalEnv finalHeap := by
  intro following anchors stack
  have first : Reaches (globals := globals) arithmetic module anchors
      ⟨.block ([.reverseSequenceStepLoop name source position body otherwise] ++ following) env, stack, heap⟩
      (1 + integer arithmetic position) ⟨.block (otherwise ++ following) env, stack, heap⟩ :=
    advance (by simp [step, finished]) (by simp [charge, finished]) rfl
  exact (first.trans (rest following anchors stack)).mono (by omega)

end FormalSW.PyAst.HeapCalls.Runtime.BlockContinuesIn
