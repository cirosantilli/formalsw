import lang.py.FormalSW.SumCalls

/-! Compositional execution rules for comprehensions with unpacked targets. -/
namespace FormalSW.PyAst.HeapCalls
variable {globals : Mutable.Globals}

/-- Prove a range comprehension by composing ordinary loop proofs. Only its
first range arguments use the enclosing scope. -/
theorem Evaluates.list_comp_targets_range
    (arguments : Arguments (globals := globals) module env expressions heap values middle)
    (bounds : rangeBounds values = .ok (start, stop, stride))
    (executed : BlockContinues (globals := globals) module
      (comprehensionTargetsEnv env ((target, .call (.name "range") expressions, filters) :: generators))
      [.rangeStepLoop (comprehensionTargetName target) start stop stride
        (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody [.comprehensionAppend middle.length element] generators))) []]
      (middle ++ [.list []]) finalEnv finalHeap) :
    Evaluates (globals := globals) module env
      (.listCompTargets element ((target, .call (.name "range") expressions, filters) :: generators))
      heap (.ref middle.length) finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach arguments _ [] anchors stack).trans
  exact .next (by simp [step, comprehensionTargetsStart, bounds])
    ((executed [] anchors (.comprehensionResult middle.length :: stack)).trans
      (.next rfl (.next rfl .refl)))

/-- The first sequence is evaluated and validated outside the comprehension's
local scope; the loop continues to read the same shared object. -/
theorem Evaluates.list_comp_targets_sequence
    (ordinary : ∀ expressions, iterable ≠ .call (.name "range") expressions)
    (evaluated : Evaluates (globals := globals) module env iterable heap value middle)
    (sequence : Mutable.sequence value middle = some (.ok items, middle))
    (executed : BlockContinues (globals := globals) module
      (comprehensionTargetsEnv env ((target, iterable, filters) :: generators))
      [.sequenceStepLoop (comprehensionTargetName target) (sequenceSource value) 0
        (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody [.comprehensionAppend middle.length element] generators))) []]
      (middle ++ [.list []]) finalEnv finalHeap) :
    Evaluates (globals := globals) module env (.listCompTargets element ((target, iterable, filters) :: generators))
      heap (.ref middle.length) finalHeap := by
  intro anchors stack
  have first : step (globals := globals) module anchors
      ⟨.expr (.listCompTargets element ((target, iterable, filters) :: generators)) env, stack, heap⟩ =
      .next (argumentsState
        (.comprehensionTargets element ((target, iterable, filters) :: generators)
          (comprehensionTargetsEnv env ((target, iterable, filters) :: generators)))
        env [] [iterable] stack heap) := by
    cases iterable <;> simp_all [step]
  apply Reaches.next first
  apply (arguments_reach (.cons evaluated .nil) _ [] anchors stack).trans
  refine .next ?_
    ((executed [] anchors (.comprehensionResult middle.length :: stack)).trans
      (.next rfl (.next rfl .refl)))
  cases iterable <;> simp_all [step, comprehensionTargetsStart, run]

/-- Generator creation evaluates its first range before the ordinary start argument. -/
theorem Evaluates.sum_generator_targets_range
    (arguments : Arguments (globals := globals) module env expressions heap values middle)
    (bounds : rangeBounds values = .ok (first, stop, stride))
    (started : Evaluates (globals := globals) module env start middle initial afterStart)
    (accepted : sumInitial initial afterStart = some (.ok initial, afterStart))
    (executed : BlockReturns (globals := globals) module
      (setLocal (comprehensionTargetsEnv env ((target, .call (.name "range") expressions, filters) :: generators))
        sumAccumulator initial)
      [.rangeStepLoop (comprehensionTargetName target) first stop stride (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody (sumBody element []) generators))) [],
        .return (.name sumAccumulator)] afterStart answer finalHeap) :
    Evaluates (globals := globals) module env
      (.sumGeneratorTargets element ((target, .call (.name "range") expressions, filters) :: generators) start)
      heap answer finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach arguments _ [] anchors stack).trans
  apply Reaches.next (following := ⟨.expr start env,
    .sumStart (.rangeStepLoop (comprehensionTargetName target) first stop stride
      (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody (sumBody element []) generators))) [])
      (comprehensionTargetsEnv env ((target, .call (.name "range") expressions, filters) :: generators)) :: stack,
    middle⟩) (by simp [step, sumGeneratorTargetsStart, bounds])
  apply (started anchors _).trans
  exact .next (by simp [step, sumEnter, run, accepted]) (executed anchors stack)

/-- The first iterator retains its identity while later generator work stays lazy. -/
theorem Evaluates.sum_generator_targets_sequence
    (ordinary : ∀ expressions, iterable ≠ .call (.name "range") expressions)
    (evaluated : Evaluates (globals := globals) module env iterable heap source middle)
    (sequence : Mutable.sequence source middle = some (.ok items, middle))
    (started : Evaluates (globals := globals) module env start middle initial afterStart)
    (accepted : sumInitial initial afterStart = some (.ok initial, afterStart))
    (executed : BlockReturns (globals := globals) module
      (setLocal (comprehensionTargetsEnv env ((target, iterable, filters) :: generators)) sumAccumulator initial)
      [.sequenceStepLoop (comprehensionTargetName target) (sequenceSource source) 0
        (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody (sumBody element []) generators))) [],
        .return (.name sumAccumulator)] afterStart answer finalHeap) :
    Evaluates (globals := globals) module env (.sumGeneratorTargets element ((target, iterable, filters) :: generators) start)
      heap answer finalHeap := by
  intro anchors stack
  have first : step (globals := globals) module anchors
      ⟨.expr (.sumGeneratorTargets element ((target, iterable, filters) :: generators) start) env, stack, heap⟩ =
      .next (argumentsState (.sumGeneratorTargets element ((target, iterable, filters) :: generators) env start)
        env [] [iterable] stack heap) := by
    cases iterable <;> simp_all [step]
  apply Reaches.next first
  apply (arguments_reach (.cons evaluated .nil) _ [] anchors stack).trans
  apply Reaches.next (following := ⟨.expr start env,
    .sumStart (.sequenceStepLoop (comprehensionTargetName target) (sequenceSource source) 0
      (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody (sumBody element []) generators))) [])
      (comprehensionTargetsEnv env ((target, iterable, filters) :: generators)) :: stack, middle⟩)
  · cases iterable <;> simp_all [step, sumGeneratorTargetsStart, run]
  apply (started anchors _).trans
  exact .next (by simp [step, sumEnter, run, accepted]) (executed anchors stack)


end FormalSW.PyAst.HeapCalls
