import lang.py.FormalSW.HeapCalls

/-! Compositional proofs for eager sequence sums and immediately consumed generators. -/

namespace FormalSW.PyAst.HeapCalls

variable {globals : Mutable.Globals}


/-- Both ordinary arguments are evaluated before acquiring the sequence iterator. -/
theorem Evaluates.sum_sequence
    (arguments : Arguments (globals := globals) module env [iterable, start] heap [source, initial] middle)
    (sequence : Mutable.sequence source middle = some (.ok items, middle))
    (accepted : sumInitial initial middle = some (.ok initial, middle))
    (executed : BlockReturns (globals := globals) module (setLocal (fun _ => none) sumAccumulator initial)
      [.sequenceStepLoop sumItem (sequenceSource source) 0 (sumBody (.name sumItem) []) [],
        .return (.name sumAccumulator)] middle answer finalHeap) :
    Evaluates (globals := globals) module env (.sumSequence iterable start) heap answer finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach arguments _ [] anchors stack).trans
  exact .next (by simp [step, sumSequenceStart, run, sequence, sumEnter, accepted])
    (executed anchors stack)

/-- Generator creation evaluates its first range before the ordinary start argument. -/
theorem Evaluates.sum_generator_range
    (arguments : Arguments (globals := globals) module env expressions heap values middle)
    (bounds : rangeBounds values = .ok (first, stop, stride))
    (started : Evaluates (globals := globals) module env start middle initial afterStart)
    (accepted : sumInitial initial afterStart = some (.ok initial, afterStart))
    (executed : BlockReturns (globals := globals) module
      (setLocal (comprehensionEnv env ((name, .call (.name "range") expressions, filters) :: generators))
        sumAccumulator initial)
      [.rangeStepLoop name first stop stride (comprehensionFilters filters (sumBody element generators)) [],
        .return (.name sumAccumulator)] afterStart answer finalHeap) :
    Evaluates (globals := globals) module env
      (.sumGenerator element ((name, .call (.name "range") expressions, filters) :: generators) start)
      heap answer finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach arguments _ [] anchors stack).trans
  apply Reaches.next (following := ⟨.expr start env,
    .sumStart (.rangeStepLoop name first stop stride
      (comprehensionFilters filters (sumBody element generators)) [])
      (comprehensionEnv env ((name, .call (.name "range") expressions, filters) :: generators)) :: stack,
    middle⟩) (by simp [step, sumGeneratorStart, bounds])
  apply (started anchors _).trans
  exact .next (by simp [step, sumEnter, run, accepted])
    ((executed anchors (.generatorEnd :: stack)).trans (.next rfl .refl))

/-- The first iterator retains its identity while later generator work stays lazy. -/
theorem Evaluates.sum_generator_sequence
    (ordinary : ∀ expressions, iterable ≠ .call (.name "range") expressions)
    (evaluated : Evaluates (globals := globals) module env iterable heap source middle)
    (sequence : Mutable.sequence source middle = some (.ok items, middle))
    (started : Evaluates (globals := globals) module env start middle initial afterStart)
    (accepted : sumInitial initial afterStart = some (.ok initial, afterStart))
    (executed : BlockReturns (globals := globals) module
      (setLocal (comprehensionEnv env ((name, iterable, filters) :: generators)) sumAccumulator initial)
      [.sequenceStepLoop name (sequenceSource source) 0
        (comprehensionFilters filters (sumBody element generators)) [],
        .return (.name sumAccumulator)] afterStart answer finalHeap) :
    Evaluates (globals := globals) module env (.sumGenerator element ((name, iterable, filters) :: generators) start)
      heap answer finalHeap := by
  intro anchors stack
  have first : step (globals := globals) module anchors
      ⟨.expr (.sumGenerator element ((name, iterable, filters) :: generators) start) env, stack, heap⟩ =
      .next (argumentsState (.sumGenerator element ((name, iterable, filters) :: generators) env start)
        env [] [iterable] stack heap) := by
    cases iterable <;> simp_all [step]
  apply Reaches.next first
  apply (arguments_reach (.cons evaluated .nil) _ [] anchors stack).trans
  apply Reaches.next (following := ⟨.expr start env,
    .sumStart (.sequenceStepLoop name (sequenceSource source) 0
      (comprehensionFilters filters (sumBody element generators)) [])
      (comprehensionEnv env ((name, iterable, filters) :: generators)) :: stack, middle⟩)
  · cases iterable <;> simp_all [step, sumGeneratorStart, run]
  apply (started anchors _).trans
  exact .next (by simp [step, sumEnter, run, accepted])
    ((executed anchors (.generatorEnd :: stack)).trans (.next rfl .refl))

/-- Preserve the legacy range-sum AST while using the heap interpreter's loop rules. -/
theorem Evaluates.sum_range
    (evaluated : Evaluates (globals := globals) module env
      (.sumGenerator element [(name, .call (.name "range") bounds, filters)] (.constant (.int 0)))
      heap answer finalHeap) :
    Evaluates (globals := globals) module env (.sumRange name element bounds filters) heap answer finalHeap :=
  fun anchors stack => .next rfl (evaluated anchors stack)

/-- Sum a pure integer-valued expression over an unchanged sequence, without a fuel bound. -/
theorem sum_map_loop {α : Type} {values : List α} {encode : α → Value} {number : α → Int}
    (remaining : List α)
    (privateName : name ≠ sumAccumulator)
    (sequence : Mutable.sequence (sequenceValue source) heap =
      some (.ok (values.map encode), heap))
    (evaluated : ∀ env item, env name = some (encode item) →
      Evaluates (globals := globals) module env element heap (.scalar (.int (number item))) heap)
    (suffix : values.drop position = remaining)
    (accumulator : env sumAccumulator = some (.scalar (.int initial))) :
    BlockReturns (globals := globals) module env
      [.sequenceStepLoop name source position (sumBody element []) [],
        .return (.name sumAccumulator)] heap
      (.scalar (.int (remaining.foldl (fun total item => total + number item) initial))) heap := by
  induction remaining generalizing position env initial with
  | nil =>
      apply BlockReturns.sequence_done sequence
      · have missing : values[position]? = none := by
          simpa [suffix] using (List.head?_drop (l := values) (i := position)).symm
        simp [missing]
      · exact BlockReturns.return_value (Evaluates.lookup accumulator)
  | cons head tail ih =>
      have item : values[position]? = some head := by
        simpa [suffix] using (List.head?_drop (l := values) (i := position)).symm
      apply BlockReturns.sequence_step (value := encode head) sequence (by simp [item])
      apply BlockReturns.assign (value := .scalar (.int (initial + number head))) (middle := heap)
      · apply Evaluates.binary (bv := .scalar (.int (number head)))
          (Evaluates.lookup (by simpa [setLocal, Ne.symm privateName] using accumulator))
          (evaluated _ head (by simp [setLocal]))
        rfl
      · change BlockReturns (globals := globals) module _
          [.sequenceStepLoop name source (position + 1) (sumBody element []) [],
            .return (.name sumAccumulator)] heap _ heap
        apply ih
        · simp [List.drop_add_one_eq_tail_drop, suffix]
        · simp [setLocal]

/-- Integer summation is the identity instance of mapped summation. -/
theorem sum_integer_loop {values : List Int} (remaining : List Int)
    (privateName : name ≠ sumAccumulator)
    (sequence : Mutable.sequence (sequenceValue source) heap =
      some (.ok (values.map (fun n => .scalar (.int n))), heap))
    (suffix : values.drop position = remaining)
    (accumulator : env sumAccumulator = some (.scalar (.int initial))) :
    BlockReturns (globals := globals) module env
      [.sequenceStepLoop name source position (sumBody (.name name) []) [],
        .return (.name sumAccumulator)] heap
      (.scalar (.int (remaining.foldl Int.add initial))) heap :=
  sum_map_loop (number := id) remaining privateName sequence
    (fun _ _ lookup => Evaluates.lookup lookup) suffix accumulator

/-- Integer summation reads the existing list or tuple and leaves the heap unchanged. -/
theorem Evaluates.sum_integers {values : List Int}
    (arguments : Arguments (globals := globals) module env [iterable, start] heap [source, .scalar (.int initial)] middle)
    (sequence : Mutable.sequence source middle =
      some (.ok (values.map (fun n => .scalar (.int n))), middle)) :
    Evaluates (globals := globals) module env (.sumSequence iterable start) heap
      (.scalar (.int (values.foldl Int.add initial))) middle := by
  apply Evaluates.sum_sequence arguments sequence rfl
  apply sum_integer_loop values (by decide)
  · cases source <;> exact sequence
  · rfl
  · simp [setLocal]

end FormalSW.PyAst.HeapCalls
