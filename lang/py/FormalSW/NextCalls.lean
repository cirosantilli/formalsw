import lang.py.FormalSW.ComprehensionCalls

/-! First-yield generator consumption and finite first-match scans. -/
namespace FormalSW.PyAst.HeapCalls

variable {globals : Mutable.Globals} {module : Module} {env : Env}
  {heap middle afterDefault finalHeap : Heap} {iterable element : Expr}
  {fallback : Option Expr} {target : Expr} {filters : List Expr}
  {generators : List (Expr × Expr × List Expr)} {source fallbackValue answer : Value}
  {items : List Value} {expressions : List Expr} {boundValues : List Value}
  {first stop stride : Int}

theorem nextSequence_list (heap : Heap) (address : Nat) (items : List Value)
    (found : heap[address]? = some (.list items)) :
    nextSequence (.ref address) heap = some (.ok items, heap) := by
  simp [nextSequence, Mutable.sequence, found]

/-- The first iterator is validated before the eager default runs outside this generator. -/
theorem Evaluates.next_generator_sequence
    (ordinary : ∀ arguments, iterable ≠ .call (.name "range") arguments)
    (notEnumerate : ∀ arguments, iterable ≠ .call (.name "enumerate") arguments)
    (notZip : ∀ arguments, iterable ≠ .zipIterable arguments)
    (evaluated : Evaluates (globals := globals) module env iterable heap source middle)
    (sequence : nextSequence source middle = some (.ok items, middle))
    (defaultEval : Evaluates (globals := globals) module env (fallback.getD (.constant .none))
      middle fallbackValue afterDefault)
    (executed : BlockReturns (globals := globals) module
      (nextEnv (comprehensionTargetsEnv env ((target, iterable, filters) :: generators))
        fallbackValue)
      ([.sequenceStepLoop (comprehensionTargetName target) (sequenceSource source) 0
        (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody [.return element] generators))) []] ++
        nextFinish fallback.isSome)
      afterDefault answer finalHeap) :
    Evaluates (globals := globals) module env
      (.consumeGenerator (nextConsumer fallback) element
        ((target, iterable, filters) :: generators)) heap answer finalHeap := by
  intro anchors stack
  have notPermutations := evaluated.not_permutations
  have notCombinations := evaluated.not_combinations
  have notDictionaryValues := evaluated.not_dictionary_values
  have arguments : nextGeneratorArguments fallback element
      ((target, iterable, filters) :: generators) env stack heap =
      argumentsState (.nextGenerator fallback element
        ((target, iterable, filters) :: generators) env) env [] [iterable] stack heap := by
    cases iterable <;> simp_all [nextGeneratorArguments]
  have initial : step (globals := globals) module anchors
      ⟨.expr (.consumeGenerator (nextConsumer fallback) element
        ((target, iterable, filters) :: generators)) env, stack, heap⟩ =
      .next (nextGeneratorArguments fallback element
        ((target, iterable, filters) :: generators) env stack heap) := by
    cases fallback <;> rfl
  rw [arguments] at initial
  apply Reaches.next initial
  apply (Evaluates.arguments_reach (.cons evaluated .nil) _ [] anchors stack).trans
  apply Reaches.next (following := ⟨.expr (fallback.getD (.constant .none)) env,
    .nextStart fallback.isSome
      (.sequenceStepLoop (comprehensionTargetName target) (sequenceSource source) 0
        (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody [.return element] generators))) [])
      (comprehensionTargetsEnv env ((target, iterable, filters) :: generators)) :: stack, middle⟩)
  · change protectGenerator stack
      (nextGeneratorStart (globals := globals) anchors fallback element
        ((target, iterable, filters) :: generators) env [source] stack middle) = _
    cases iterable <;> simp_all [nextGeneratorStart, run]
  apply (defaultEval anchors _).trans
  exact .next rfl ((executed anchors (.generatorEnd :: stack)).trans (.next rfl .refl))

theorem Evaluates.next_generator_range
    (arguments : Evaluates.Arguments (globals := globals) module env expressions
      heap boundValues middle)
    (bounds : rangeBounds boundValues = .ok (first, stop, stride))
    (defaultEval : Evaluates (globals := globals) module env (fallback.getD (.constant .none))
      middle fallbackValue afterDefault)
    (executed : BlockReturns (globals := globals) module
      (nextEnv (comprehensionTargetsEnv env
        ((target, .call (.name "range") expressions, filters) :: generators)) fallbackValue)
      ([.rangeStepLoop (comprehensionTargetName target) first stop stride
        (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody [.return element] generators))) []] ++
        nextFinish fallback.isSome)
      afterDefault answer finalHeap) :
    Evaluates (globals := globals) module env
      (.consumeGenerator (nextConsumer fallback) element
        ((target, .call (.name "range") expressions, filters) :: generators))
      heap answer finalHeap := by
  intro anchors stack
  have initial : step (globals := globals) module anchors
      ⟨.expr (.consumeGenerator (nextConsumer fallback) element
        ((target, .call (.name "range") expressions, filters) :: generators)) env, stack, heap⟩ =
      .next (argumentsState (.nextGenerator fallback element
        ((target, .call (.name "range") expressions, filters) :: generators) env)
        env [] expressions stack heap) := by
    cases fallback <;> rfl
  apply Reaches.next initial
  apply (Evaluates.arguments_reach arguments _ [] anchors stack).trans
  apply Reaches.next (following := ⟨.expr (fallback.getD (.constant .none)) env,
    .nextStart fallback.isSome
      (.rangeStepLoop (comprehensionTargetName target) first stop stride
        (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody [.return element] generators))) [])
      (comprehensionTargetsEnv env
        ((target, .call (.name "range") expressions, filters) :: generators)) :: stack, middle⟩)
  · simp [step, nextGeneratorStart, bounds]
  apply (defaultEval anchors _).trans
  exact .next rfl ((executed anchors (.generatorEnd :: stack)).trans (.next rfl .refl))

/-- A pure predicate scans every finite suffix up to its first match, retaining captures. -/
theorem find_sequence_loop {α : Type} (values : List α) (encode : α → Value)
    (predicate : α → Bool) (condition element fallback : Expr) (name : String)
    (source : SequenceSource) (heap : Heap) (defaultValue : Value)
    (invariant : Env → Prop)
    (preserved : ∀ inner item, invariant inner → invariant (setLocal inner name (encode item)))
    (tested : ∀ inner item, invariant inner → inner name = some (encode item) →
      Evaluates (globals := globals) module inner condition heap
        (.scalar (.bool (predicate item))) heap)
    (emitted : ∀ inner item, invariant inner → inner name = some (encode item) →
      Evaluates (globals := globals) module inner element heap (encode item) heap)
    (defaultEval : ∀ inner, invariant inner →
      Evaluates (globals := globals) module inner fallback heap defaultValue heap)
    (remaining : List α) (env : Env) (position : Nat)
    (sequence : Mutable.sequence (sequenceValue source) heap =
      some (.ok (values.map encode), heap))
    (valid : invariant env) (suffix : values.drop position = remaining) :
    BlockReturns (globals := globals) module env
      [.sequenceStepLoop name source position [.ifThen condition [.return element] []] [],
        .return fallback] heap
      (((remaining.find? predicate).map encode).getD defaultValue) heap := by
  induction remaining generalizing position env with
  | nil =>
      apply BlockReturns.sequence_done sequence
      · have missing : values[position]? = none := by
          simpa [suffix] using (List.head?_drop (l := values) (i := position)).symm
        simp [missing]
      · exact BlockReturns.return_value (defaultEval env valid)
  | cons head tail ih =>
      have item : values[position]? = some head := by
        simpa [suffix] using (List.head?_drop (l := values) (i := position)).symm
      let bound := setLocal env name (encode head)
      have boundValid : invariant bound := preserved env head valid
      have lookup : bound name = some (encode head) := by simp [bound, setLocal]
      have evaluated := tested bound head boundValid lookup
      apply BlockReturns.sequence_step (value := encode head) sequence (by simp [item])
      cases accepted : predicate head with
      | true =>
          simp only [List.find?_cons, accepted, Option.map_some, Option.getD_some]
          apply BlockReturns.branch (flag := true) (by simpa only [accepted] using evaluated) rfl
          exact BlockReturns.return_value (emitted bound head boundValid lookup)
      | false =>
          simp only [List.find?_cons, accepted]
          apply BlockReturns.branch (flag := false) (by simpa only [accepted] using evaluated) rfl
          have rest := ih bound (position + 1) boundValid
            (by simp [List.drop_add_one_eq_tail_drop, suffix])
          simpa [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, bound] using rest

end FormalSW.PyAst.HeapCalls
