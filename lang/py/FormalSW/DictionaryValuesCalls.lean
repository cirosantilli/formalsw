import lang.py.FormalSW.DictionaryItemsCalls
import lang.py.FormalSW.ComprehensionCalls

/-! Source rules for immediately consumed, live dictionary values. -/
namespace FormalSW.PyAst.HeapCalls
variable {globals : Mutable.Globals}

/-- The receiver is evaluated once, then the existing cursor reads current dictionary values. -/
theorem BlockContinues.for_dictionary_values
    (receiver : Evaluates (globals := globals) module env expression heap (.ref address) middle)
    (found : middle[address]? = some object) (fields : dictionaryItemFields object = some entries)
    (rest : BlockContinues (globals := globals) module env
      [.dictionaryItemsStepLoop "$formalsw.values.pair" address
        (entries.map fun entry => sequenceSource entry.1) 0 (dictionaryValuesBody target body) otherwise]
      middle finalEnv finalHeap) :
    BlockContinues (globals := globals) module env
      [.forIn target (.dictionaryValuesIterable expression) body otherwise] heap finalEnv finalHeap := by
  intro following anchors stack
  apply Reaches.next rfl
  apply (receiver anchors _).trans
  exact .next (by simp [step, dictionaryValuesStart, found, fields]) (rest following anchors stack)

theorem BlockReturns.for_dictionary_values
    (receiver : Evaluates (globals := globals) module env expression heap (.ref address) middle)
    (found : middle[address]? = some object) (fields : dictionaryItemFields object = some entries)
    (rest : BlockReturns (globals := globals) module env
      (.dictionaryItemsStepLoop "$formalsw.values.pair" address
        (entries.map fun entry => sequenceSource entry.1) 0 (dictionaryValuesBody target body) otherwise :: following)
      middle answer finalHeap) :
    BlockReturns (globals := globals) module env
      (.forIn target (.dictionaryValuesIterable expression) body otherwise :: following) heap answer finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (receiver anchors _).trans
  exact .next (by simp [step, dictionaryValuesStart, found, fields]) (rest anchors stack)

/-- Iterator creation precedes collector allocation, and only source target names are masked in the body. -/
theorem Evaluates.list_comp_dictionary_values
    (receiver : Evaluates (globals := globals) module env expression heap (.ref address) middle)
    (found : middle[address]? = some object) (fields : dictionaryItemFields object = some entries)
    (executed : BlockContinues (globals := globals) module
      (comprehensionTargetsEnv env ((target, .dictionaryValuesIterable expression, filters) :: generators))
      [.dictionaryItemsStepLoop "$formalsw.values.pair" address
        (entries.map fun entry => sequenceSource entry.1) 0
        (dictionaryValuesBody target (comprehensionFilters filters
          (comprehensionTargetsBody [.comprehensionAppend middle.length element] generators))) []]
      (middle ++ [.list []]) finalEnv finalHeap) :
    Evaluates (globals := globals) module env
      (.listCompTargets element ((target, .dictionaryValuesIterable expression, filters) :: generators))
      heap (.ref middle.length) finalHeap := by
  have preserved : (middle ++ [Mutable.Object.list []])[address]? = some object := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach (.cons receiver .nil) _ [] anchors stack).trans
  exact .next (by simp [step, comprehensionTargetsStart, dictionaryValuesCollectionStart,
      dictionaryValuesStart, found, preserved, fields])
    ((executed [] anchors (.comprehensionResult middle.length :: stack)).trans
      (.next rfl (.next rfl .refl)))

end FormalSW.PyAst.HeapCalls
