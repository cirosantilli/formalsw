import lang.py.FormalSW.HeapMemoCallRules

/-! Sequence and enumerate loops whose bodies allocate or reuse cached heap objects. -/
namespace FormalSW.PyAst.HeapMemoCalls
variable {globals : Mutable.Globals}

namespace BlockReturnsRel

/-- An ordinary iterable expression can precede a cache-aware loop body. -/
theorem for_sequence_heap (disjoint : CacheDisjoint module module)
    (ordinary : ∀ expressions, iterable ≠ .call (.name "range") expressions)
    (evaluated : HeapCalls.Evaluates module env iterable heap value middle globals)
    (preserved : Cache.Preserves spec heap middle)
    (sequence : Mutable.sequence value middle = some (.ok items, middle))
    (rest : BlockReturnsRel module spec env
      (.sequenceStepLoop name (HeapCalls.sequenceSource value) 0 body otherwise :: following) middle post globals) :
    BlockReturnsRel module spec env (.forIn (.name name) iterable body otherwise :: following) heap post globals := by
  intro anchors stack
  have start : HeapCalls.step module anchors
      ⟨.block (.forIn (.name name) iterable body otherwise :: following) env, stack, heap⟩ globals =
      .next ⟨.expr iterable env, .sequence name body otherwise following env :: stack, heap⟩ := by
    have notPermutations := evaluated.not_permutations
    have notCombinations := evaluated.not_combinations
    have notDictionaryValues := evaluated.not_dictionary_values
    cases iterable <;> simp_all [HeapCalls.step]
  apply RunsRel.next (by trivial) start
  apply ((Evaluates.from_heap (HeapCalls.Extends.refl _) disjoint evaluated preserved) anchors _).bind
  rintro final rfl
  exact RunsRel.next (by trivial) (by simp [HeapCalls.step, HeapCalls.run, sequence]) (rest anchors stack)

/-- The default enumerate counter is initialized once, before any body effect. -/
theorem for_enumerate
    (iterable : Evaluates module spec env expression heap source middle globals)
    (sequence : Mutable.sequence source middle = some (.ok items, middle))
    (rest : BlockReturnsRel module spec env
      (.enumerateStepLoop index name (HeapCalls.sequenceSource source) 0 0 body otherwise :: following) middle post globals) :
    BlockReturnsRel module spec env
      (.forIn (.tuple [.name index, .name name]) (.call (.name "enumerate") [expression]) body otherwise :: following)
      heap post globals := by
  intro anchors stack
  apply RunsRel.next (by trivial) rfl
  apply (iterable anchors _).bind
  rintro final rfl
  exact RunsRel.next (by trivial) rfl (RunsRel.next (by trivial) rfl
    (RunsRel.next (by trivial) (by simp [HeapCalls.step, HeapCalls.run, HeapCalls.enumerateStart, sequence])
      (rest anchors stack)))

/-- Enumerate reads the live sequence and binds the index before the item. -/
theorem enumerate_step
    (sequence : Mutable.sequence (HeapCalls.sequenceValue source) heap = some (.ok items, heap))
    (item : items[position]? = some value)
    (rest : BlockReturnsRel module spec
      (HeapCalls.setLocal (HeapCalls.setLocal env index (.scalar (.int counter))) name value)
      (body ++ [Calls.loopContinuation body
        (.enumerateStepLoop index name source (position + 1) (counter + 1) body otherwise)] ++ following)
      heap post globals) :
    BlockReturnsRel module spec env
      (.enumerateStepLoop index name source position counter body otherwise :: following) heap post globals := by
  intro anchors stack
  exact RunsRel.next (by trivial) (by simp [HeapCalls.step, HeapCalls.run, sequence, item]) (rest anchors stack)

theorem enumerate_done
    (sequence : Mutable.sequence (HeapCalls.sequenceValue source) heap = some (.ok items, heap))
    (finished : items[position]? = none)
    (rest : BlockReturnsRel module spec env (otherwise ++ following) heap post globals) :
    BlockReturnsRel module spec env
      (.enumerateStepLoop index name source position counter body otherwise :: following) heap post globals := by
  intro anchors stack
  exact RunsRel.next (by trivial) (by simp [HeapCalls.step, HeapCalls.run, sequence, finished]) (rest anchors stack)

end BlockReturnsRel
end FormalSW.PyAst.HeapMemoCalls
