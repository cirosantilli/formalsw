import lang.py.FormalSW.DictionaryItemsCalls

/-! Source composition for sums over fresh live dictionary item iterators. -/
namespace FormalSW.PyAst.HeapCalls
variable {globals : Mutable.Globals}

/-- Acquire the first item cursor before the start argument; later bindings, filters and elements stay lazy. -/
theorem Evaluates.sum_generator_items
    (receiver : Evaluates (globals := globals) module env expression heap (.ref address) middle)
    (found : middle[address]? = some object) (fields : dictionaryItemFields object = some entries)
    (started : Evaluates (globals := globals) module env start middle initial afterStart)
    (accepted : sumInitial initial afterStart = some (.ok initial, afterStart))
    (executed : BlockReturns (globals := globals) module
      (setLocal (comprehensionTargetsEnv env
        ((target, .call (.attribute expression "items") [], filters) :: generators)) sumAccumulator initial)
      [.dictionaryItemsStepLoop (comprehensionTargetName target) address
        (entries.map fun entry => sequenceSource entry.1) 0
        (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody (sumBody element []) generators))) [],
        .return (.name sumAccumulator)] afterStart answer finalHeap) :
    Evaluates (globals := globals) module env
      (.sumGeneratorTargets element
        ((target, .call (.attribute expression "items") [], filters) :: generators) start)
      heap answer finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach (.cons receiver .nil) _ [] anchors stack).trans
  apply Reaches.next (following := ⟨.expr start env,
    .sumStart (.dictionaryItemsStepLoop (comprehensionTargetName target) address
      (entries.map fun entry => sequenceSource entry.1) 0
      (comprehensionTargetBody target (comprehensionFilters filters
        (comprehensionTargetsBody (sumBody element []) generators))) [])
      (comprehensionTargetsEnv env ((target, .call (.attribute expression "items") [], filters) :: generators)) :: stack,
    middle⟩) (by simp [step, sumGeneratorTargetsStart, itemsReceiver, dictionaryItemsSumStart, found, fields])
  apply (started anchors _).trans
  exact .next (by simp [step, sumEnter, run, accepted])
    ((executed anchors (.generatorEnd :: stack)).trans (.next rfl .refl))

end FormalSW.PyAst.HeapCalls
