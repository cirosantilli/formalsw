import lang.py.FormalSW.HeapRuntimeCostListLoops

namespace FormalSW.PyAst.HeapCalls.Runtime
open PrimitiveWork

/-- Function-local annotations do not evaluate the annotation expression. -/
theorem BlockContinuesIn.annAssign
    (evaluated : EvaluatesIn arithmetic module env expression heap cost value finalHeap) :
    BlockContinuesIn arithmetic module env [.annAssign (.name name) annotation (some expression)] heap
      (cost+2) (setLocal env name value) finalHeap := by
  intro following anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.block ([.annAssign (.name name) annotation (some expression)] ++ following) env, stack, heap⟩ 1
      ⟨.expr expression env, .assign name following env :: stack, heap⟩ := advance rfl rfl rfl
  have last : Reaches arithmetic module anchors
      ⟨.value value, .assign name following env :: stack, finalHeap⟩ 1
      ⟨.block following (setLocal env name value), stack, finalHeap⟩ := advance rfl rfl rfl
  exact ((first.trans (evaluated anchors _)).trans last).mono (by omega)

theorem BlockContinuesIn.unpack_step
    (found : heap[address]? = some (.list items)) (fetched : items[position]? = some (.ref pair))
    (fields : heap[pair]? = some (.tuple values)) (arity : names.length = values.length)
    (rest : BlockContinuesIn .word module (assignNames env names values)
      (body ++ [Calls.loopContinuation body (.unpackStepLoop names (.ref address) (position+1) body otherwise)])
      heap budget finalEnv finalHeap) :
    BlockContinuesIn .word module env [.unpackStepLoop names (.ref address) position body otherwise]
      heap (budget+values.length+names.length+7) finalEnv finalHeap := by
  intro following anchors stack
  have first : Reaches .word module anchors
      ⟨.block ([.unpackStepLoop names (.ref address) position body otherwise] ++ following) env, stack, heap⟩
      (values.length+names.length+7)
      ⟨.block ((body ++ [Calls.loopContinuation body (.unpackStepLoop names (.ref address) (position+1) body otherwise)]) ++ following)
        (assignNames env names values), stack, heap⟩ :=
    advance (by simp [step, run, sequenceValue, Mutable.sequence, found, fetched, fields, arity, List.append_assoc])
      (by simp [charge, unpackIteration, found, fetched, sequenceLength, fields, integer]; omega) rfl
  exact (first.trans (rest following anchors stack)).mono (by omega)

theorem BlockContinuesIn.unpack_done
    (found : heap[address]? = some (.list items)) (finished : items[position]? = none)
    (rest : BlockContinuesIn .word module env otherwise heap budget finalEnv finalHeap) :
    BlockContinuesIn .word module env [.unpackStepLoop names (.ref address) position body otherwise]
      heap (budget+5) finalEnv finalHeap := by
  intro following anchors stack
  have first : Reaches .word module anchors
      ⟨.block ([.unpackStepLoop names (.ref address) position body otherwise] ++ following) env, stack, heap⟩ 5
      ⟨.block (otherwise ++ following) env, stack, heap⟩ :=
    advance (by simp [step, run, sequenceValue, Mutable.sequence, found, finished])
      (by simp [charge, unpackIteration, found, finished, integer]) rfl
  exact (first.trans (rest following anchors stack)).mono (by omega)

theorem BlockContinuesIn.for_unpack_name
    (targetsValid : Calls.targetNames targets = some names)
    (lookup : env receiver = some (.ref address)) (found : heap[address]? = some (.list items))
    (rest : BlockContinuesIn arithmetic module env [.unpackStepLoop names (.ref address) 0 body otherwise]
      heap budget finalEnv finalHeap) :
    BlockContinuesIn arithmetic module env [.forIn (.tuple targets) (.name receiver) body otherwise]
      heap (budget+targets.length+3) finalEnv finalHeap := by
  intro following anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.block ([.forIn (.tuple targets) (.name receiver) body otherwise] ++ following) env, stack, heap⟩ (targets.length+1)
      ⟨.expr (.name receiver) env, .unpackSequence names body otherwise following env :: stack, heap⟩ :=
    advance (by simp [step, targetsValid]) (by simp [charge, unpackEntry, targetsValid]) rfl
  have loaded := EvaluatesIn.lookup (globals := []) (arithmetic := arithmetic) (module := module) (heap := heap) lookup anchors
    (.unpackSequence names body otherwise following env :: stack)
  have ready : Reaches arithmetic module anchors
      ⟨.value (.ref address), .unpackSequence names body otherwise following env :: stack, heap⟩ 1
      ⟨.block ([.unpackStepLoop names (.ref address) 0 body otherwise] ++ following) env, stack, heap⟩ :=
    advance (by simp [step, run, Mutable.sequence, found, sequenceSource]) (by simp [charge, sequenceLength, found]) rfl
  exact (((first.trans loaded).trans ready).trans (rest following anchors stack)).mono (by omega)

end FormalSW.PyAst.HeapCalls.Runtime
