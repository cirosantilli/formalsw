import lang.py.FormalSW.ComprehensionCalls

/-! Immediate generator consumers reuse ordinary comprehension loop proofs.
The generator boundary ends before sorting or validating the joined strings. -/
namespace FormalSW.PyAst.HeapCalls
variable {globals : Mutable.Globals}

def GeneratorFinishes (action : GeneratorAction) (heap : Heap) (address : Nat)
    (value : Value) (finalHeap : Heap) : Prop :=
  match action with
  | .list => value = .ref address ∧ finalHeap = heap
  | .sorted => primitive (.builtin .sorted) [.ref address] heap = some (.ok value, finalHeap)
  | .join separator => primitive (.join separator) [.ref address] heap = some (.ok value, finalHeap)

theorem GeneratorFinishes.reaches
    (finished : GeneratorFinishes action heap address value finalHeap) (anchors : Nat) (stack : List Frame) :
    Reaches (globals := globals) module anchors
      ⟨.value (.ref address), .generatorConsumer action :: stack, heap⟩
      ⟨.value value, stack, finalHeap⟩ := by
  cases action with
  | list =>
      obtain ⟨rfl, rfl⟩ := finished
      exact .next rfl .refl
  | sorted =>
      change primitive (.builtin .sorted) [.ref address] heap = some (.ok value, finalHeap) at finished
      exact .next rfl (.next (by simp [step, result, run, finished]) .refl)
  | join separator =>
      change primitive (.join separator) [.ref address] heap = some (.ok value, finalHeap) at finished
      exact .next rfl (.next (by simp [step, result, run, finished]) .refl)

/-- Collect a generator whose first iterable is still in the enclosing scope. -/
def GeneratorCollects (module : Module) (action : GeneratorAction) (element : Expr)
    (generators : List (Expr × Expr × List Expr)) (env : Env) (heap : Heap)
    (value : Value) (finalHeap : Heap) (globals : Mutable.Globals := []) : Prop :=
  ∀ anchors stack, Reaches (globals := globals) module anchors
    (generatorArguments action element generators env stack heap) ⟨.value value, stack, finalHeap⟩

theorem GeneratorCollects.range
    (arguments : Evaluates.Arguments (globals := globals) module env expressions heap values middle)
    (bounds : rangeBounds values = .ok (start, stop, stride))
    (executed : BlockContinues (globals := globals) module
      (comprehensionTargetsEnv env ((target, .call (.name "range") expressions, filters) :: generators))
      [.rangeStepLoop (comprehensionTargetName target) start stop stride
        (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody [.comprehensionAppend middle.length element] generators))) []]
      (middle ++ [.list []]) finalEnv collectedHeap)
    (finished : GeneratorFinishes action collectedHeap middle.length value finalHeap) :
    GeneratorCollects (globals := globals) module action element
      ((target, .call (.name "range") expressions, filters) :: generators) env heap value finalHeap := by
  intro anchors stack
  apply (Evaluates.arguments_reach arguments _ [] anchors stack).trans
  exact .next (by simp [step, comprehensionTargetsStart, bounds])
    ((executed [] anchors (.comprehensionResult middle.length :: .generatorEnd :: .generatorConsumer action :: stack)).trans
      (.next rfl (.next rfl (.next rfl (finished.reaches anchors stack)))))

theorem GeneratorCollects.sequence
    (ordinary : ∀ expressions, iterable ≠ .call (.name "range") expressions)
    (notEnumerate : ∀ expressions, iterable ≠ .call (.name "enumerate") expressions)
    (notZip : ∀ expressions, iterable ≠ .zipIterable expressions)
    (evaluated : Evaluates (globals := globals) module env iterable heap source middle)
    (sequence : Mutable.sequence source middle = some (.ok items, middle))
    (executed : BlockContinues (globals := globals) module
      (comprehensionTargetsEnv env ((target, iterable, filters) :: generators))
      [.sequenceStepLoop (comprehensionTargetName target) (sequenceSource source) 0
        (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody [.comprehensionAppend middle.length element] generators))) []]
      (middle ++ [.list []]) finalEnv collectedHeap)
    (finished : GeneratorFinishes action collectedHeap middle.length value finalHeap) :
    GeneratorCollects (globals := globals) module action element
      ((target, iterable, filters) :: generators) env heap value finalHeap := by
  intro anchors stack
  have initial : generatorArguments action element ((target, iterable, filters) :: generators) env stack heap =
      argumentsState (.generatorCollect action element ((target, iterable, filters) :: generators)
        (comprehensionTargetsEnv env ((target, iterable, filters) :: generators))) env [] [iterable] stack heap := by
    have notPermutations := evaluated.not_permutations
    cases iterable <;> simp_all [generatorArguments]
  rw [initial]
  apply (Evaluates.arguments_reach (.cons evaluated .nil) _ [] anchors stack).trans
  refine .next ?_
    ((executed [] anchors (.comprehensionResult middle.length :: .generatorEnd :: .generatorConsumer action :: stack)).trans
      (.next rfl (.next rfl (.next rfl (finished.reaches anchors stack)))))
  have notPermutations := evaluated.not_permutations
  cases iterable <;> simp_all [step, comprehensionTargetsStart, run]

/-- Copy the remaining elements of a shared list into the private collector. -/
theorem BlockContinues.collect_sequence (heap : Heap) (address : Nat) (items remaining : List Value)
    (found : heap[address]? = some (.list items)) (position : Nat)
    (suffix : items.drop position = remaining) (collected : List Value) (env : Env) (name : String) :
    ∃ finalEnv, BlockContinues (globals := globals) module env
      [.sequenceStepLoop name (.ref address) position [.comprehensionAppend heap.length (.name name)] []]
      (heap ++ [.list collected]) finalEnv (heap ++ [.list (collected ++ remaining)]) := by
  have inside : address < heap.length := by
    by_cases inside : address < heap.length
    · exact inside
    · have missing := List.getElem?_eq_none (Nat.le_of_not_gt inside)
      simp [missing] at found
  have sequence (collected : List Value) : Mutable.sequence (.ref address) (heap ++ [.list collected]) =
      some (.ok items, heap ++ [.list collected]) := by
    simp [Mutable.sequence, List.getElem?_append_left inside, found]
  induction remaining generalizing position collected env with
  | nil =>
      simp only [List.append_nil]
      refine ⟨env, BlockContinues.sequence_done (source := .ref address) (sequence collected) ?_ .nil⟩
      simpa [suffix] using (List.head?_drop (l := items) (i := position)).symm
  | cons head tail ih =>
      let boundEnv := setLocal env name head
      have emitted : BlockContinues (globals := globals) module boundEnv
          [.comprehensionAppend heap.length (.name name)] (heap ++ [.list collected]) boundEnv
          (heap ++ [.list (collected ++ [head])]) := by
        have write := BlockContinues.comprehension_append
          (globals := globals) (module := module) (env := boundEnv) (address := heap.length)
          (heap := heap ++ [.list collected]) (Evaluates.lookup (name := name) (value := head) (by simp [boundEnv, setLocal]))
          (by simp : (heap ++ [.list collected])[heap.length]? = some (.list collected))
        simpa using write
      obtain ⟨finalEnv, rest⟩ := ih (position + 1)
        (by simp [List.drop_add_one_eq_tail_drop, suffix]) (collected ++ [head]) boundEnv
      refine ⟨finalEnv, ?_⟩
      have item : items[position]? = some head := by
        simpa [suffix] using (List.head?_drop (l := items) (i := position)).symm
      apply BlockContinues.sequence_step (source := .ref address) (value := head) (sequence collected) item
      simpa [Calls.loopContinuation, Calls.loopControl, List.append_assoc] using emitted.append rest

theorem GeneratorCollects.copy_sequence
    (lookup : env sourceName = some (.ref address))
    (found : heap[address]? = some (.list items))
    (finished : GeneratorFinishes action (heap ++ [.list items]) heap.length value finalHeap) :
    GeneratorCollects (globals := globals) module action (.name name)
      [(.name name, .name sourceName, [])] env heap value finalHeap := by
  obtain ⟨finalEnv, executed⟩ := BlockContinues.collect_sequence (globals := globals) (module := module)
    heap address items items found 0 rfl []
    (comprehensionTargetsEnv env [(.name name, .name sourceName, [])]) name
  apply GeneratorCollects.sequence (finalEnv := finalEnv) (items := items) (source := .ref address)
    (middle := heap) (collectedHeap := heap ++ [.list items])
    (by intro expressions impossible; cases impossible)
    (by intro expressions impossible; cases impossible)
    (by intro expressions impossible; cases impossible)
    (Evaluates.lookup lookup) (by simp [Mutable.sequence, found])
  · exact executed
  · exact finished

theorem Evaluates.consume_generator_list
    (collected : GeneratorCollects (globals := globals) module .list element generators env heap value finalHeap) :
    Evaluates (globals := globals) module env (.consumeGenerator (.builtinCall .list []) element generators)
      heap value finalHeap := fun anchors stack => .next rfl (collected anchors stack)

theorem Evaluates.consume_generator_sorted
    (collected : GeneratorCollects (globals := globals) module .sorted element generators env heap value finalHeap) :
    Evaluates (globals := globals) module env (.consumeGenerator (.builtinCall .sorted []) element generators)
      heap value finalHeap := fun anchors stack => .next rfl (collected anchors stack)

theorem Evaluates.consume_generator_join
    (receiver : Evaluates (globals := globals) module env base heap (.scalar (.string separator)) middle)
    (collected : GeneratorCollects (globals := globals) module (.join separator) element generators env middle value finalHeap) :
    Evaluates (globals := globals) module env (.consumeGenerator (.attribute base "join") element generators)
      heap value finalHeap := by
  intro anchors stack
  exact .next rfl ((receiver anchors _).trans
    (.next (by simp [step, run, bindMethod]) (collected anchors stack)))

end FormalSW.PyAst.HeapCalls
