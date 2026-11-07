import lang.py.FormalSW.HeapRuntimeCostListCopies

/-! List iteration retains the receiver identity and reads its current contents.
No traversal or element copy is hidden in iterator setup. -/
namespace FormalSW.PyAst.HeapCalls.Runtime.BlockReturnsIn
open PrimitiveWork

/-- Acquire the iterator after evaluating the subscription, retaining any copy or mutation. -/
theorem for_list_subscript
    (evaluated : EvaluatesIn arithmetic module env (.subscript receiver index) heap cost (.ref address) middle)
    (found : middle[address]? = some (.list items))
    (rest : BlockReturnsIn arithmetic module env
      (.sequenceStepLoop name (.ref address) 0 body otherwise :: following) middle budget answer finalHeap) :
    BlockReturnsIn arithmetic module env
      (.forIn (.name name) (.subscript receiver index) body otherwise :: following)
      heap (cost+budget+2) answer finalHeap := by
  intro anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.block (.forIn (.name name) (.subscript receiver index) body otherwise :: following) env, stack, heap⟩ 1
      ⟨.expr (.subscript receiver index) env, .sequence name body otherwise following env :: stack, heap⟩ :=
    advance rfl rfl rfl
  have next : Reaches arithmetic module anchors
      ⟨.value (.ref address), .sequence name body otherwise following env :: stack, middle⟩ 1
      ⟨.block (.sequenceStepLoop name (.ref address) 0 body otherwise :: following) env, stack, middle⟩ :=
    advance (by simp [step, run, Mutable.sequence, found, sequenceSource]) (by simp [charge, found]) rfl
  exact (((first.trans (evaluated anchors _)).trans next).trans (rest anchors stack)).mono (by omega)

/-- A stored list field is evaluated before the iterator retains its identity. -/
theorem for_list_field
    (evaluated : EvaluatesIn arithmetic module env (.attribute receiver fieldName) heap cost (.ref address) middle)
    (found : middle[address]? = some (.list items))
    (rest : BlockReturnsIn arithmetic module env
      (.sequenceStepLoop name (.ref address) 0 body otherwise :: following) middle budget answer finalHeap) :
    BlockReturnsIn arithmetic module env
      (.forIn (.name name) (.attribute receiver fieldName) body otherwise :: following)
      heap (cost+budget+2) answer finalHeap := by
  intro anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.block (.forIn (.name name) (.attribute receiver fieldName) body otherwise :: following) env, stack, heap⟩ 1
      ⟨.expr (.attribute receiver fieldName) env, .sequence name body otherwise following env :: stack, heap⟩ :=
    advance rfl rfl rfl
  have next : Reaches arithmetic module anchors
      ⟨.value (.ref address), .sequence name body otherwise following env :: stack, middle⟩ 1
      ⟨.block (.sequenceStepLoop name (.ref address) 0 body otherwise :: following) env, stack, middle⟩ :=
    advance (by simp [step, run, Mutable.sequence, found, sequenceSource]) (by simp [charge, found]) rfl
  exact (((first.trans (evaluated anchors _)).trans next).trans (rest anchors stack)).mono (by omega)

theorem for_list_name (lookup : env receiver = some (.ref address))
    (found : heap[address]? = some (.list items))
    (rest : BlockReturnsIn arithmetic module env
      (.sequenceStepLoop name (.ref address) 0 body otherwise :: following) heap budget answer finalHeap) :
    BlockReturnsIn arithmetic module env (.forIn (.name name) (.name receiver) body otherwise :: following)
      heap (budget+3) answer finalHeap := by
  intro anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.block (.forIn (.name name) (.name receiver) body otherwise :: following) env, stack, heap⟩ 1
      ⟨.expr (.name receiver) env, .sequence name body otherwise following env :: stack, heap⟩ := advance rfl rfl rfl
  have loaded := EvaluatesIn.lookup (arithmetic := arithmetic) (module := module) (heap := heap) lookup anchors
    (.sequence name body otherwise following env :: stack)
  have next : Reaches arithmetic module anchors
      ⟨.value (.ref address), .sequence name body otherwise following env :: stack, heap⟩ 1
      ⟨.block (.sequenceStepLoop name (.ref address) 0 body otherwise :: following) env, stack, heap⟩ :=
    advance (by simp [step, run, Mutable.sequence, found, sequenceSource]) (by simp [charge, found]) rfl
  exact (((first.trans loaded).trans next).trans (rest anchors stack)).mono (by omega)

theorem list_step (found : heap[address]? = some (.list items))
    (item : items[position]? = some value)
    (rest : BlockReturnsIn .word module (setLocal env name value)
      (body ++ [Calls.loopContinuation body (.sequenceStepLoop name (.ref address) (position+1) body otherwise)] ++ following)
      heap budget answer finalHeap) :
    BlockReturnsIn .word module env (.sequenceStepLoop name (.ref address) position body otherwise :: following)
      heap (budget+5) answer finalHeap := by
  intro anchors stack
  have first : Reaches .word module anchors
      ⟨.block (.sequenceStepLoop name (.ref address) position body otherwise :: following) env, stack, heap⟩ 5
      ⟨.block (body ++ [Calls.loopContinuation body (.sequenceStepLoop name (.ref address) (position+1) body otherwise)] ++ following)
        (setLocal env name value), stack, heap⟩ :=
    advance (by simp [step, run, sequenceValue, Mutable.sequence, found, item]) (by simp [charge, found, integer]) rfl
  exact (first.trans (rest anchors stack)).mono (by omega)

theorem list_done (found : heap[address]? = some (.list items))
    (finished : items[position]? = none)
    (rest : BlockReturnsIn .word module env (otherwise ++ following) heap budget answer finalHeap) :
    BlockReturnsIn .word module env (.sequenceStepLoop name (.ref address) position body otherwise :: following)
      heap (budget+5) answer finalHeap := by
  intro anchors stack
  have first : Reaches .word module anchors
      ⟨.block (.sequenceStepLoop name (.ref address) position body otherwise :: following) env, stack, heap⟩ 5
      ⟨.block (otherwise ++ following) env, stack, heap⟩ :=
    advance (by simp [step, run, sequenceValue, Mutable.sequence, found, finished])
      (by simp [charge, found, integer]) rfl
  exact (first.trans (rest anchors stack)).mono (by omega)

end FormalSW.PyAst.HeapCalls.Runtime.BlockReturnsIn
