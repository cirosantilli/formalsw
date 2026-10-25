import lang.py.FormalSW.ComprehensionCalls

/-! Compositional rules for fresh zip iterators over shared builtin sequences. -/
namespace FormalSW.PyAst.HeapCalls
variable {globals : Mutable.Globals}

/-- Evaluate all zip arguments before acquiring the private sequence iterators. -/
theorem BlockReturns.for_zip
    (arguments : Evaluates.Arguments (globals := globals) module env expressions heap values middle)
    (captured : zipSources values middle = some (.ok sources, middle))
    (rest : BlockReturns (globals := globals) module env
      (.zipStepLoop (comprehensionTargetName target) sources 0
        (comprehensionTargetBody target body) otherwise :: following)
      middle answer finalHeap) :
    BlockReturns (globals := globals) module env (.forZip target expressions body otherwise :: following) heap answer finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (Evaluates.arguments_reach arguments _ [] anchors stack).trans
  exact .next (by simp [step, run, captured]) (rest anchors stack)

/-- A successful zip step creates one tuple, retaining every field's identity. -/
theorem BlockReturns.zip_step
    (fetched : zipItem sources position heap = some (.ok (some fields), middle))
    (allocated : Mutable.allocateTuple fields middle = some (.ok tuple, afterTuple))
    (rest : BlockReturns (globals := globals) module (setLocal env name tuple)
      (body ++ [Calls.loopContinuation body (.zipStepLoop name sources (position + 1) body otherwise)] ++ following)
      afterTuple answer finalHeap) :
    BlockReturns (globals := globals) module env
      (.zipStepLoop name sources position body otherwise :: following)
      heap answer finalHeap := by
  intro anchors stack
  refine .next ?_ (rest anchors stack)
  simp [step, run, fetched, allocated]

/-- Exhaustion runs the loop's else block without allocating another tuple. -/
theorem BlockReturns.zip_done
    (finished : zipItem sources position heap = some (.ok none, middle))
    (rest : BlockReturns (globals := globals) module env (otherwise ++ following) middle answer finalHeap) :
    BlockReturns (globals := globals) module env
      (.zipStepLoop name sources position body otherwise :: following)
      heap answer finalHeap :=
  fun anchors stack =>
    .next (by simp [step, run, finished]) (rest anchors stack)

/-- Evaluate all zip arguments before acquiring the private sequence iterators. -/
theorem BlockContinues.for_zip
    (arguments : Evaluates.Arguments (globals := globals) module env expressions heap values middle)
    (captured : zipSources values middle = some (.ok sources, middle))
    (rest : BlockContinues (globals := globals) module env
      [.zipStepLoop (comprehensionTargetName target) sources 0
        (comprehensionTargetBody target body) otherwise]
      middle finalEnv finalHeap) :
    BlockContinues (globals := globals) module env [.forZip target expressions body otherwise] heap finalEnv finalHeap := by
  intro following anchors stack
  apply Reaches.next rfl
  apply (Evaluates.arguments_reach arguments _ [] anchors stack).trans
  exact .next (by simp [step, run, captured]) (rest following anchors stack)

/-- A successful zip step creates one tuple, retaining every field's identity. -/
theorem BlockContinues.zip_step
    (fetched : zipItem sources position heap = some (.ok (some fields), middle))
    (allocated : Mutable.allocateTuple fields middle = some (.ok tuple, afterTuple))
    (rest : BlockContinues (globals := globals) module (setLocal env name tuple)
      (body ++ [Calls.loopContinuation body (.zipStepLoop name sources (position + 1) body otherwise)])
      afterTuple finalEnv finalHeap) :
    BlockContinues (globals := globals) module env
      [.zipStepLoop name sources position body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  refine .next ?_ (rest following anchors stack)
  simp [step, run, fetched, allocated, List.append_assoc]

/-- Exhaustion runs the loop's else block without allocating another tuple. -/
theorem BlockContinues.zip_done
    (finished : zipItem sources position heap = some (.ok none, middle))
    (rest : BlockContinues (globals := globals) module env otherwise middle finalEnv finalHeap) :
    BlockContinues (globals := globals) module env
      [.zipStepLoop name sources position body otherwise]
      heap finalEnv finalHeap :=
  fun following anchors stack =>
    .next (by simp [step, run, finished]) (rest following anchors stack)

/-- The first zip is captured in the enclosing scope before the private result list. -/
theorem Evaluates.list_comp_targets_zip
    (arguments : Arguments (globals := globals) module env expressions heap values middle)
    (captured : zipSources values middle = some (.ok sources, middle))
    (executed : BlockContinues (globals := globals) module
      (comprehensionTargetsEnv env ((target, .zipIterable expressions, filters) :: generators))
      [.zipStepLoop (comprehensionTargetName target) sources 0
        (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody [.comprehensionAppend middle.length element] generators))) []]
      (middle ++ [.list []]) finalEnv finalHeap) :
    Evaluates (globals := globals) module env
      (.listCompTargets element ((target, .zipIterable expressions, filters) :: generators))
      heap (.ref middle.length) finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach arguments _ [] anchors stack).trans
  exact .next (by simp [step, comprehensionTargetsStart, run, captured])
    ((executed [] anchors (.comprehensionResult middle.length :: stack)).trans
      (.next rfl (.next rfl .refl)))

/-- Sum captures zip's sources before evaluating its start; iteration then reads the live heap. -/
theorem Evaluates.sum_generator_targets_zip
    (arguments : Arguments (globals := globals) module env expressions heap values middle)
    (captured : zipSources values middle = some (.ok sources, middle))
    (started : Evaluates (globals := globals) module env start middle initial afterStart)
    (accepted : sumInitial initial afterStart = some (.ok initial, afterStart))
    (executed : BlockReturns (globals := globals) module
      (setLocal (comprehensionTargetsEnv env ((target, .zipIterable expressions, filters) :: generators))
        sumAccumulator initial)
      [.zipStepLoop (comprehensionTargetName target) sources 0
        (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody (sumBody element []) generators))) [],
        .return (.name sumAccumulator)] afterStart answer finalHeap) :
    Evaluates (globals := globals) module env
      (.sumGeneratorTargets element ((target, .zipIterable expressions, filters) :: generators) start)
      heap answer finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach arguments _ [] anchors stack).trans
  apply Reaches.next (following := ⟨.expr start env,
    .sumStart (.zipStepLoop (comprehensionTargetName target) sources 0
      (comprehensionTargetBody target (comprehensionFilters filters
        (comprehensionTargetsBody (sumBody element []) generators))) [])
      (comprehensionTargetsEnv env ((target, .zipIterable expressions, filters) :: generators)) :: stack,
    middle⟩) (by simp [step, sumGeneratorTargetsStart, run, captured])
  apply (started anchors _).trans
  exact .next (by simp [step, sumEnter, run, accepted])
    ((executed anchors (.generatorEnd :: stack)).trans (.next rfl .refl))

end FormalSW.PyAst.HeapCalls
