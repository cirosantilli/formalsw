import lang.py.FormalSW.HeapCalls

/-! Short-circuiting truth consumers over ordinary sequences and lazy generators.
The generator rules retain filters, nested iterables, and the generator exception
boundary. Pure mapped predicates need no collector allocation. -/
namespace FormalSW.PyAst.HeapCalls
variable {globals : Mutable.Globals}

theorem Evaluates.truth_sequence
    (arguments : Arguments (globals := globals) module env [iterable] heap [source] middle)
    (sequence : Mutable.sequence source middle = some (.ok items, middle))
    (executed : BlockReturns (globals := globals) module (fun _ => none)
      [.sequenceStepLoop sumItem (sequenceSource source) 0 (truthBody universal (.name sumItem)) [],
        .return (.constant (.bool universal))] middle answer finalHeap) :
    Evaluates (globals := globals) module env
      (.builtinCall (if universal then .all else .any) [iterable]) heap answer finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach arguments _ [] anchors stack).trans
  refine .next ?_ (executed anchors stack)
  cases universal <;> simp [step, truthSequenceStart, run, sequence]

theorem Evaluates.truth_generator_range
    (arguments : Arguments (globals := globals) module env expressions heap values middle)
    (bounds : rangeBounds values = .ok (first, stop, stride))
    (executed : BlockReturns (globals := globals) module
      (comprehensionTargetsEnv env ((target, .call (.name "range") expressions, filters) :: generators))
      [.rangeStepLoop (comprehensionTargetName target) first stop stride
        (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody (truthBody universal element) generators))) [],
        .return (.constant (.bool universal))] middle answer finalHeap) :
    Evaluates (globals := globals) module env
      (.consumeGenerator (.builtinCall (if universal then .all else .any) []) element
        ((target, .call (.name "range") expressions, filters) :: generators))
      heap answer finalHeap := by
  intro anchors stack
  have initial : step (globals := globals) module anchors
      ⟨.expr (.consumeGenerator (.builtinCall (if universal then .all else .any) []) element
        ((target, .call (.name "range") expressions, filters) :: generators)) env, stack, heap⟩ =
      .next (argumentsState (.truthGenerator universal element
        ((target, .call (.name "range") expressions, filters) :: generators)
        (comprehensionTargetsEnv env
          ((target, .call (.name "range") expressions, filters) :: generators)))
        env [] expressions stack heap) := by
    cases universal <;> rfl
  apply Reaches.next initial
  apply (arguments_reach arguments _ [] anchors stack).trans
  exact .next (by simp [step, truthGeneratorStart, bounds])
    ((executed anchors (.generatorEnd :: stack)).trans (.next rfl .refl))

theorem Evaluates.truth_generator_sequence
    (ordinary : ∀ expressions, iterable ≠ .call (.name "range") expressions)
    (notEnumerate : ∀ expressions, iterable ≠ .call (.name "enumerate") expressions)
    (notZip : ∀ expressions, iterable ≠ .zipIterable expressions)
    (evaluated : Evaluates (globals := globals) module env iterable heap source middle)
    (sequence : Mutable.sequence source middle = some (.ok items, middle))
    (executed : BlockReturns (globals := globals) module
      (comprehensionTargetsEnv env ((target, iterable, filters) :: generators))
      [.sequenceStepLoop (comprehensionTargetName target) (sequenceSource source) 0
        (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody (truthBody universal element) generators))) [],
        .return (.constant (.bool universal))] middle answer finalHeap) :
    Evaluates (globals := globals) module env
      (.consumeGenerator (.builtinCall (if universal then .all else .any) []) element
        ((target, iterable, filters) :: generators)) heap answer finalHeap := by
  intro anchors stack
  have notPermutations := evaluated.not_permutations
  have arguments : truthGeneratorArguments universal element ((target, iterable, filters) :: generators)
      env stack heap =
      argumentsState (.truthGenerator universal element ((target, iterable, filters) :: generators)
        (comprehensionTargetsEnv env ((target, iterable, filters) :: generators)))
        env [] [iterable] stack heap := by
    cases iterable <;> simp_all [truthGeneratorArguments]
  have initial : step (globals := globals) module anchors
      ⟨.expr (.consumeGenerator (.builtinCall (if universal then .all else .any) []) element
        ((target, iterable, filters) :: generators)) env, stack, heap⟩ =
      .next (truthGeneratorArguments universal element ((target, iterable, filters) :: generators)
        env stack heap) := by
    cases universal <;> rfl
  rw [arguments] at initial
  apply Reaches.next initial
  apply (arguments_reach (.cons evaluated .nil) _ [] anchors stack).trans
  have entered : truthGeneratorStart (globals := globals) anchors universal element
      ((target, iterable, filters) :: generators)
      (comprehensionTargetsEnv env ((target, iterable, filters) :: generators))
      [source] stack middle =
      .next ⟨.block
        [.sequenceStepLoop (comprehensionTargetName target) (sequenceSource source) 0
          (comprehensionTargetBody target (comprehensionFilters filters
            (comprehensionTargetsBody (truthBody universal element) generators))) [],
          .return (.constant (.bool universal))]
        (comprehensionTargetsEnv env ((target, iterable, filters) :: generators)),
        .generatorEnd :: stack, middle⟩ := by
    cases iterable <;> simp_all [truthGeneratorStart, run]
  exact .next (by simp only [step, List.nil_append, entered, protectGenerator_next])
    ((executed anchors (.generatorEnd :: stack)).trans (.next rfl .refl))

/-- A lazy existential range scan preserves captured locals through an explicit invariant. -/
theorem any_range_loop (invariant : Env → Prop) (predicate : Nat → Bool)
    (preserved : ∀ inner (n : Nat), invariant inner → invariant (setLocal inner name (.scalar (.int n))))
    (evaluated : ∀ inner (n : Nat), invariant inner → inner name = some (.scalar (.int n)) →
      Evaluates (globals := globals) module inner element heap (.scalar (.bool (predicate n))) heap)
    (first count stop : Nat) (length : first+count=stop) (valid : invariant env) :
    BlockReturns (globals := globals) module env
      [.rangeStepLoop name first stop 1 (truthBody false element) [],
        .return (.constant (.bool false))]
      heap (.scalar (.bool ((List.range' first count).any predicate))) heap := by
  induction count generalizing first env with
  | zero =>
      apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
      exact BlockReturns.return_value Evaluates.constant
  | succ count ih =>
      let bound := setLocal env name (.scalar (.int first))
      have validBound : invariant bound := preserved env first valid
      have tested := evaluated bound first validBound (by simp [bound, setLocal])
      rw [List.range'_succ, List.any_cons]
      apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
      cases accepted : predicate first with
      | true =>
          simp only [Bool.true_or]
          apply BlockReturns.branch (flag := true) (by simpa only [accepted] using tested) rfl
          exact BlockReturns.return_value Evaluates.constant
      | false =>
          simp only [Bool.false_or]
          apply BlockReturns.branch (flag := false) (by simpa only [accepted] using tested) rfl
          have rest := ih (first+1) (by omega) validBound
          simpa only [truthBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
            Bool.false_or, Bool.false_eq_true, if_false, List.nil_append,
            Int.natCast_add, Int.natCast_one] using rest

/-- A pure boolean predicate stops at its first false element. -/
theorem all_map_loop {α : Type} {values : List α} {encode : α → Value} {predicate : α → Bool}
    (remaining : List α)
    (sequence : Mutable.sequence (sequenceValue source) heap =
      some (.ok (values.map encode), heap))
    (evaluated : ∀ env item, env name = some (encode item) →
      Evaluates (globals := globals) module env element heap (.scalar (.bool (predicate item))) heap)
    (suffix : values.drop position = remaining) :
    BlockReturns (globals := globals) module env
      [.sequenceStepLoop name source position (truthBody true element) [],
        .return (.constant (.bool true))] heap
      (.scalar (.bool (remaining.all predicate))) heap := by
  induction remaining generalizing position env with
  | nil =>
      apply BlockReturns.sequence_done sequence
      · have missing : values[position]? = none := by
          simpa [suffix] using (List.head?_drop (l := values) (i := position)).symm
        simp [missing]
      · exact BlockReturns.return_value Evaluates.constant
  | cons head tail ih =>
      have item : values[position]? = some head := by
        simpa [suffix] using (List.head?_drop (l := values) (i := position)).symm
      apply BlockReturns.sequence_step (value := encode head) sequence (by simp [item])
      have headEvaluated := evaluated (setLocal env name (encode head)) head (by simp [setLocal])
      cases flag : predicate head with
      | false =>
          rw [flag] at headEvaluated
          simp only [List.all_cons, flag, Bool.false_and]
          apply BlockReturns.branch headEvaluated rfl
          exact BlockReturns.return_value Evaluates.constant
      | true =>
          rw [flag] at headEvaluated
          simp only [List.all_cons, flag, Bool.true_and]
          apply BlockReturns.branch headEvaluated rfl
          have rest := ih (position := position + 1)
            (env := setLocal env name (encode head))
            (by simp [List.drop_add_one_eq_tail_drop, suffix])
          simpa [truthBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt] using rest

/-- Map a pure boolean predicate lazily over an existing sequence. -/
theorem Evaluates.all_map {α : Type} {values : List α} {encode : α → Value} {predicate : α → Bool}
    (ordinary : ∀ expressions, iterable ≠ .call (.name "range") expressions)
    (notEnumerate : ∀ expressions, iterable ≠ .call (.name "enumerate") expressions)
    (notZip : ∀ expressions, iterable ≠ .zipIterable expressions)
    (evaluated : Evaluates (globals := globals) module env iterable heap source middle)
    (sequence : Mutable.sequence source middle = some (.ok (values.map encode), middle))
    (elementValue : ∀ inner item, inner name = some (encode item) →
      Evaluates (globals := globals) module inner element middle (.scalar (.bool (predicate item))) middle) :
    Evaluates (globals := globals) module env
      (.consumeGenerator (.builtinCall .all []) element [(.name name, iterable, [])]) heap
      (.scalar (.bool (values.all predicate))) middle := by
  apply Evaluates.truth_generator_sequence (universal := true)
    ordinary notEnumerate notZip evaluated sequence
  apply all_map_loop values
  · cases source <;> exact sequence
  · exact elementValue
  · rfl

/-- Integer positivity over a list or tuple preserves the heap and lexical scope. -/
theorem Evaluates.all_positive {values : List Int}
    (evaluated : Evaluates (globals := globals) module env (.name sourceName) heap source middle)
    (sequence : Mutable.sequence source middle =
      some (.ok (values.map (fun n => .scalar (.int n))), middle)) :
    Evaluates (globals := globals) module env
      (.consumeGenerator (.builtinCall .all [])
        (.compare (.name name) [(.gt, .constant (.int 0))]) [(.name name, .name sourceName, [])]) heap
      (.scalar (.bool (decide (∀ n ∈ values, 0 < n)))) middle := by
  have mapped := Evaluates.all_map (name := name) (values := values)
    (encode := fun n => .scalar (.int n)) (predicate := fun n => decide (0 < n))
    (element := .compare (.name name) [(.gt, .constant (.int 0))])
    (by intros; simp) (by intros; simp) (by intros; simp) evaluated sequence
    (fun _ _ lookup => Evaluates.compare (Evaluates.lookup lookup) Evaluates.constant rfl)
  simpa only [List.all_eq, decide_eq_true_eq] using mapped

end FormalSW.PyAst.HeapCalls
