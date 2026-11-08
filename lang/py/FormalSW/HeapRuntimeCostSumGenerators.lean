import lang.py.FormalSW.HeapRuntimeCostListLoops

namespace FormalSW.PyAst.HeapCalls.Runtime

/-- The builtin iterator reads one element or detects its end in fixed work. -/
def ConstantSequenceRead (module : Module) (heap : Heap) (source : SequenceSource) : Prop :=
  ∀ name position body otherwise following env stack,
    charge .word module ⟨.block (.sequenceStepLoop name source position body otherwise :: following) env,
      stack, heap⟩ = some 5

/-- Pure mapped summation preserves the sequence and charges the element expression each time. -/
theorem sum_sequence_loop {α : Type} {values : List α} {encode : α → Value} {number : α → Int}
    (remaining : List α) (position : Nat) (itemCost : Nat)
    (privateName : name ≠ sumAccumulator)
    (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok (values.map encode), heap))
    (priced : ConstantSequenceRead module heap source)
    (evaluated : ∀ env item, env name = some (encode item) →
      EvaluatesIn .word module env element heap itemCost (.scalar (.int (number item))) heap)
    (suffix : values.drop position = remaining)
    (accumulator : env sumAccumulator = some (.scalar (.int initial))) :
    BlockReturnsIn .word module env
      [.sequenceStepLoop name source position (sumBody element []) [], .return (.name sumAccumulator)] heap
      ((itemCost+12)*remaining.length+7)
      (.scalar (.int (remaining.foldl (fun total item => total + number item) initial))) heap := by
  induction remaining generalizing position env initial with
  | nil =>
      have missing : values[position]? = none := by
        simpa [suffix] using (List.head?_drop (l := values) (i := position)).symm
      intro anchors stack
      have head : Reaches .word module anchors
          ⟨.block [.sequenceStepLoop name source position (sumBody element []) [],
              .return (.name sumAccumulator)] env, stack, heap⟩ 5
          ⟨.block [.return (.name sumAccumulator)] env, stack, heap⟩ :=
        advance (by simp [step, run, sequence, missing]) (priced ..) rfl
      exact head.trans (BlockReturnsIn.return_value (EvaluatesIn.lookup accumulator) anchors stack)
  | cons item rest ih =>
      have found : values[position]? = some item := by
        simpa [suffix] using (List.head?_drop (l := values) (i := position)).symm
      have itemRun := evaluated (setLocal env name (encode item)) item (by simp [setLocal])
      have addition : EvaluatesIn .word module (setLocal env name (encode item))
          (.binOp (.name sumAccumulator) .add element) heap (itemCost+5)
          (.scalar (.int (initial+number item))) heap := by
        have run := EvaluatesIn.binary (op := .add) (av := .int initial) (bv := .int (number item))
          (work := 1) (EvaluatesIn.lookup (name := sumAccumulator) (by simpa [setLocal, Ne.symm privateName] using accumulator)) itemRun rfl rfl
        exact run.mono (by omega)
      have tail := ih (position+1) (initial := initial+number item)
        (env := setLocal (setLocal env name (encode item)) sumAccumulator (.scalar (.int (initial+number item))))
        (by simp [List.drop_add_one_eq_tail_drop, suffix]) (by simp [setLocal])
      intro anchors stack
      have head : Reaches .word module anchors
          ⟨.block [.sequenceStepLoop name source position (sumBody element []) [],
              .return (.name sumAccumulator)] env, stack, heap⟩ 5
          ⟨.block (sumBody element [] ++ [.sequenceStepLoop name source (position+1) (sumBody element []) [],
              .return (.name sumAccumulator)]) (setLocal env name (encode item)), stack, heap⟩ :=
        advance (by simp [step, run, sequence, found, sumBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt])
          (priced ..) rfl
      exact (head.trans (BlockReturnsIn.assign addition tail anchors stack)).mono (by simp [Nat.mul_add]; omega)

/-- Acquire a builtin sequence once, then execute a single unfiltered generator lazily. -/
theorem EvaluatesIn.sum_generator
    (ordinary : ∀ expressions, iterable ≠ .call (.name "range") expressions)
    (iterated : EvaluatesIn .word module env iterable heap ca source middle)
    (sequence : Mutable.sequence source middle = some (.ok items, middle))
    (length : sequenceLength middle source = some size)
    (started : EvaluatesIn .word module env start middle cb (.scalar (.int initial)) afterStart)
    (loop : BlockReturnsIn .word module
      (setLocal (comprehensionEnv env [(name, iterable, [])]) sumAccumulator (.scalar (.int initial)))
      [.sequenceStepLoop name (sequenceSource source) 0 (sumBody element []) [],
        .return (.name sumAccumulator)] afterStart budget answer finalHeap) :
    EvaluatesIn .word module env (.sumGenerator element [(name, iterable, [])] start) heap
      (ca+cb+budget+8) answer finalHeap := by
  intro anchors stack
  have first : Reaches .word module anchors
      ⟨.expr (.sumGenerator element [(name, iterable, [])] start) env, stack, heap⟩ 1
      (argumentsState (.sumGenerator element [(name, iterable, [])] env start) env [] [iterable] stack heap) :=
    advance (by cases iterable <;> simp_all [step]) rfl rfl
  have arguments := (ArgumentsIn.cons iterated ArgumentsIn.nil).reaches
    (completed := []) (.sumGenerator element [(name, iterable, [])] env start) anchors stack
  have ready : Reaches .word module anchors
      ⟨.operation (.sumGenerator element [(name, iterable, [])] env start) [source], stack, middle⟩ 3
      ⟨.expr start env, .sumStart
        (.sequenceStepLoop name (sequenceSource source) 0 (sumBody element []) [])
        (comprehensionEnv env [(name, iterable, [])]) :: stack, middle⟩ :=
    advance (by cases iterable <;> simp_all [step, sumGeneratorStart, run, comprehensionFilters])
      (by simp [charge, operation, length]) rfl
  have enter : Reaches .word module anchors
      ⟨.value (.scalar (.int initial)), .sumStart
        (.sequenceStepLoop name (sequenceSource source) 0 (sumBody element []) [])
        (comprehensionEnv env [(name, iterable, [])]) :: stack, afterStart⟩ 2
      ⟨.block [.sequenceStepLoop name (sequenceSource source) 0 (sumBody element []) [],
          .return (.name sumAccumulator)]
        (setLocal (comprehensionEnv env [(name, iterable, [])]) sumAccumulator (.scalar (.int initial))),
        .generatorEnd :: stack, afterStart⟩ := advance rfl rfl rfl
  have finish : Reaches .word module anchors
      ⟨.value answer, .generatorEnd :: stack, finalHeap⟩ 1
      ⟨.value answer, stack, finalHeap⟩ := advance rfl rfl rfl
  exact ((((((first.trans arguments).trans ready).trans (started anchors _)).trans enter).trans
    (loop anchors (.generatorEnd :: stack))).trans finish).mono (by simp; omega)

end FormalSW.PyAst.HeapCalls.Runtime
