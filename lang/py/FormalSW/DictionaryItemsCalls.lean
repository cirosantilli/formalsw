import lang.py.FormalSW.HeapCalls

/-! Compositional rules for immediate iteration over dictionaries' live items. -/
namespace FormalSW.PyAst.HeapCalls
variable {globals : Mutable.Globals}

/-- Replacements preserve captured keys but values are read from the current heap. -/
theorem dictionaryItemsNext_fields (found : heap[address]?=some object)
    (fields : dictionaryItemFields object=some entries) :
    dictionaryItemsNext address (entries.map fun entry => sequenceSource entry.1) position heap=
      some (.ok entries[position]?, heap) := by
  simp [dictionaryItemsNext, found, fields]

theorem dictionaryItemsNext_dict (found : heap[address]?=some (.dict entries)) :
    dictionaryItemsNext address (entries.map fun entry => SequenceSource.scalar entry.1) position heap=
      some (.ok (entries[position]?.map fun entry => (Mutable.Value.scalar entry.1, entry.2)), heap) := by
  simpa only [List.map_map, Function.comp_def, sequenceSource, List.getElem?_map] using
    dictionaryItemsNext_fields (position := position) found (rfl : dictionaryItemFields (.dict entries)=_)

/-- The receiver is evaluated once before creating the private iterator. -/
theorem BlockReturns.for_dictionary_items
    (receiver : Evaluates (globals := globals) module env expression heap (.ref address) middle)
    (found : middle[address]?=some object) (fields : dictionaryItemFields object=some entries)
    (rest : BlockReturns (globals := globals) module env
      (.dictionaryItemsStepLoop (comprehensionTargetName target) address (entries.map fun entry => sequenceSource entry.1) 0
        (comprehensionTargetBody target body) otherwise :: following) middle answer finalHeap) :
    BlockReturns (globals := globals) module env
      (.forDictionaryItems target expression body otherwise :: following) heap answer finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (receiver anchors _).trans
  exact .next (by simp [step, dictionaryItemsStart, found, fields]) (rest anchors stack)

/-- Each successful next creates a pair sharing its key and value with the dictionary. -/
theorem BlockReturns.dictionary_items_step
    (fetched : dictionaryItemsNext address keys position heap=some (.ok (some (key,value)), middle))
    (allocated : Mutable.allocateTuple [key,value] middle=some (.ok pair, afterTuple))
    (rest : BlockReturns (globals := globals) module (setLocal env name pair)
      (body ++ [Calls.loopContinuation body (.dictionaryItemsStepLoop name address keys (position+1) body otherwise)] ++ following)
      afterTuple answer finalHeap) :
    BlockReturns (globals := globals) module env
      (.dictionaryItemsStepLoop name address keys position body otherwise :: following) heap answer finalHeap := by
  intro anchors stack
  exact .next (by simp [step, run, fetched, allocated]) (rest anchors stack)

/-- The final next checks the dictionary before running the loop's else block. -/
theorem BlockReturns.dictionary_items_done
    (finished : dictionaryItemsNext address keys position heap=some (.ok none, middle))
    (rest : BlockReturns (globals := globals) module env (otherwise++following) middle answer finalHeap) :
    BlockReturns (globals := globals) module env
      (.dictionaryItemsStepLoop name address keys position body otherwise :: following) heap answer finalHeap :=
  fun anchors stack => .next (by simp [step, run, finished]) (rest anchors stack)

theorem BlockContinues.for_dictionary_items
    (receiver : Evaluates (globals := globals) module env expression heap (.ref address) middle)
    (found : middle[address]?=some object) (fields : dictionaryItemFields object=some entries)
    (rest : BlockContinues (globals := globals) module env
      [.dictionaryItemsStepLoop (comprehensionTargetName target) address (entries.map fun entry => sequenceSource entry.1) 0
        (comprehensionTargetBody target body) otherwise] middle finalEnv finalHeap) :
    BlockContinues (globals := globals) module env [.forDictionaryItems target expression body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  apply Reaches.next rfl
  apply (receiver anchors _).trans
  exact .next (by simp [step, dictionaryItemsStart, found, fields]) (rest following anchors stack)

theorem BlockContinues.dictionary_items_step
    (fetched : dictionaryItemsNext address keys position heap=some (.ok (some (key,value)), middle))
    (allocated : Mutable.allocateTuple [key,value] middle=some (.ok pair, afterTuple))
    (rest : BlockContinues (globals := globals) module (setLocal env name pair)
      (body ++ [Calls.loopContinuation body (.dictionaryItemsStepLoop name address keys (position+1) body otherwise)])
      afterTuple finalEnv finalHeap) :
    BlockContinues (globals := globals) module env
      [.dictionaryItemsStepLoop name address keys position body otherwise] heap finalEnv finalHeap := by
  intro following anchors stack
  refine .next ?_ (rest following anchors stack)
  simp [step, run, fetched, allocated, List.append_assoc]

theorem BlockContinues.dictionary_items_done
    (finished : dictionaryItemsNext address keys position heap=some (.ok none, middle))
    (rest : BlockContinues (globals := globals) module env otherwise middle finalEnv finalHeap) :
    BlockContinues (globals := globals) module env
      [.dictionaryItemsStepLoop name address keys position body otherwise] heap finalEnv finalHeap :=
  fun following anchors stack => .next (by simp [step, run, finished]) (rest following anchors stack)

end FormalSW.PyAst.HeapCalls
