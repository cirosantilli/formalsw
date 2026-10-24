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
    (notEnumerate : ∀ expressions, iterable ≠ .call (.name "enumerate") expressions)
    (notZip : ∀ expressions, iterable ≠ .zipIterable expressions)
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
    (notEnumerate : ∀ expressions, iterable ≠ .call (.name "enumerate") expressions)
    (notZip : ∀ expressions, iterable ≠ .zipIterable expressions)
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


/-- Enumerate acquires its first iterator before the generator sum's start is evaluated. -/
theorem Evaluates.sum_generator_targets_enumerate
    (arguments : Arguments (globals := globals) module env [iterable, counterExpression] heap [source, startValue] middle)
    (counter : enumerateStart startValue middle = some (.ok first, middle))
    (sequence : Mutable.sequence source middle = some (.ok items, middle))
    (pair : enumerateTarget target = some (index, name))
    (started : Evaluates (globals := globals) module env start middle initial afterStart)
    (accepted : sumInitial initial afterStart = some (.ok initial, afterStart))
    (executed : BlockReturns (globals := globals) module
      (setLocal (comprehensionTargetsEnv env
        ((target, .call (.name "enumerate") [iterable, counterExpression], filters) :: generators)) sumAccumulator initial)
      [.enumerateStepLoop index name (sequenceSource source) 0 first
        (comprehensionFilters filters (comprehensionTargetsBody (sumBody element []) generators)) [],
        .return (.name sumAccumulator)] afterStart answer finalHeap) :
    Evaluates (globals := globals) module env
      (.sumGeneratorTargets element
        ((target, .call (.name "enumerate") [iterable, counterExpression], filters) :: generators) start)
      heap answer finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach arguments _ [] anchors stack).trans
  apply Reaches.next (following := ⟨.expr start env,
    .sumStart (.enumerateStepLoop index name (sequenceSource source) 0 first
      (comprehensionFilters filters (comprehensionTargetsBody (sumBody element []) generators)) [])
      (comprehensionTargetsEnv env
        ((target, .call (.name "enumerate") [iterable, counterExpression], filters) :: generators)) :: stack,
    middle⟩) (by simp [step, sumGeneratorTargetsStart, pair, run, counter, sequence])
  apply (started anchors _).trans
  exact .next (by simp [step, sumEnter, run, accepted]) (executed anchors stack)

/-- Eager enumeration validates its iterable before allocating a comprehension result. -/
theorem Evaluates.list_comp_targets_enumerate
    (arguments : Arguments (globals := globals) module env [iterable, counterExpression] heap [source, startValue] middle)
    (counter : enumerateStart startValue middle = some (.ok first, middle))
    (sequence : Mutable.sequence source middle = some (.ok items, middle))
    (pair : enumerateTarget target = some (index, name))
    (executed : BlockContinues (globals := globals) module
      (comprehensionTargetsEnv env
        ((target, .call (.name "enumerate") [iterable, counterExpression], filters) :: generators))
      [.enumerateStepLoop index name (sequenceSource source) 0 first
        (comprehensionFilters filters (comprehensionTargetsBody [.comprehensionAppend middle.length element] generators)) []]
      (middle ++ [.list []]) finalEnv finalHeap) :
    Evaluates (globals := globals) module env
      (.listCompTargets element
        ((target, .call (.name "enumerate") [iterable, counterExpression], filters) :: generators))
      heap (.ref middle.length) finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach arguments _ [] anchors stack).trans
  exact .next (by simp [step, comprehensionTargetsStart, pair, run, counter, sequence])
    ((executed [] anchors (.comprehensionResult middle.length :: stack)).trans
      (.next rfl (.next rfl .refl)))

/-- A returning enumerate loop binds its index before the current value. -/
theorem BlockReturns.enumerate_step
    (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (item : items[position]? = some value)
    (rest : BlockReturns (globals := globals) module (setLocal (setLocal env index (.scalar (.int counter))) name value)
      (body ++ [Calls.loopContinuation body
        (.enumerateStepLoop index name source (position + 1) (counter + 1) body otherwise)] ++ following)
      heap answer finalHeap) :
    BlockReturns (globals := globals) module env
      (.enumerateStepLoop index name source position counter body otherwise :: following) heap answer finalHeap := by
  intro anchors stack
  exact .next (by simp [step, run, sequence, item]) (rest anchors stack)

theorem BlockReturns.enumerate_done
    (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (finished : items[position]? = none)
    (rest : BlockReturns (globals := globals) module env (otherwise ++ following) heap answer finalHeap) :
    BlockReturns (globals := globals) module env
      (.enumerateStepLoop index name source position counter body otherwise :: following) heap answer finalHeap := by
  intro anchors stack
  exact .next (by simp [step, run, sequence, finished]) (rest anchors stack)

/-- Indexed summation keeps Python's arbitrary signed starting index. -/
def indexedSum {α : Type} (number : Int → α → Int) (start initial : Int) : List α → Int
  | [] => initial
  | head :: tail => indexedSum number (start + 1) (initial + number start head) tail

/-- Sum a pure integer-valued expression over an unchanged enumerated sequence. -/
theorem sum_enumerate_loop {α : Type} {values : List α} {encode : α → Value} {number : Int → α → Int}
    (remaining : List α) (distinct : index ≠ name)
    (privateIndex : index ≠ sumAccumulator) (privateName : name ≠ sumAccumulator)
    (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok (values.map encode), heap))
    (evaluated : ∀ env counter item, env index = some (.scalar (.int counter)) → env name = some (encode item) →
      Evaluates (globals := globals) module env element heap (.scalar (.int (number counter item))) heap)
    (suffix : values.drop position = remaining)
    (accumulator : env sumAccumulator = some (.scalar (.int initial))) :
    BlockReturns (globals := globals) module env
      [.enumerateStepLoop index name source position counter (sumBody element []) [], .return (.name sumAccumulator)]
      heap (.scalar (.int (indexedSum number counter initial remaining))) heap := by
  induction remaining generalizing position env counter initial with
  | nil =>
      apply BlockReturns.enumerate_done sequence
      · have missing : values[position]? = none := by
          simpa [suffix] using (List.head?_drop (l := values) (i := position)).symm
        simp [missing]
      · exact BlockReturns.return_value (Evaluates.lookup accumulator)
  | cons head tail ih =>
      have item : values[position]? = some head := by
        simpa [suffix] using (List.head?_drop (l := values) (i := position)).symm
      apply BlockReturns.enumerate_step (value := encode head) sequence (by simp [item])
      apply BlockReturns.assign (value := .scalar (.int (initial + number counter head))) (middle := heap)
      · apply Evaluates.binary (bv := .scalar (.int (number counter head)))
          (Evaluates.lookup (by simpa [setLocal, Ne.symm privateIndex, Ne.symm privateName] using accumulator))
          (evaluated _ counter head (by simp [setLocal, distinct]) (by simp [setLocal]))
        rfl
      · change BlockReturns (globals := globals) module _
          [.enumerateStepLoop index name source (position + 1) (counter + 1) (sumBody element []) [],
            .return (.name sumAccumulator)] heap _ heap
        apply ih
        · simp [List.drop_add_one_eq_tail_drop, suffix]
        · simp [setLocal]

end FormalSW.PyAst.HeapCalls
