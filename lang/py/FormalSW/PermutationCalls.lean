import lang.py.FormalSW.GeneratorCalls

/-! Source loop rules for private positional permutation iterators. -/
namespace FormalSW.PyAst.HeapCalls
variable {globals : Mutable.Globals}

theorem tuple_allocates (items : List Value) (heap : Heap) :
    ∃ value finalHeap, Mutable.allocateTuple items heap = some (.ok value, finalHeap) := by
  cases items with
  | nil =>
      cases found : heap.findIdx? (fun object => decide (object = .tuple [])) with
      | none => exact ⟨.ref heap.length, heap ++ [.tuple []], by simp [Mutable.allocateTuple, found, Except.map]⟩
      | some address => exact ⟨.ref address, heap, by simp [Mutable.allocateTuple, found]⟩
  | cons head tail =>
      exact ⟨.ref heap.length, heap ++ [.tuple (head :: tail)], by simp [Mutable.allocateTuple, Except.map]⟩

theorem permutationRows_list (heap : Heap) (address : Nat) (items : List Value)
    (found : heap[address]? = some (.list items)) :
    permutationRows [.ref address, .scalar .none] heap =
      some (.ok ((Permutations.rows items.length items).map (List.map sequenceSource)), heap) := by
  simp [permutationRows, Permutations.acquire_list heap address items found]

theorem BlockReturns.for_permutations
    (arguments : Evaluates.Arguments (globals := globals) module env expressions heap values middle)
    (captured : permutationRows values middle = some (.ok rows, middle))
    (rest : BlockReturns (globals := globals) module env
      (.permutationStepLoop (comprehensionTargetName target) rows
        (comprehensionTargetBody target body) otherwise :: following) middle answer finalHeap) :
    BlockReturns (globals := globals) module env
      (.forIn target (.permutationsIterable expressions) body otherwise :: following) heap answer finalHeap := by
  intro anchors stack
  exact .next rfl ((Evaluates.arguments_reach arguments _ [] anchors stack).trans
    (.next (by simp [step, run, captured]) (rest anchors stack)))

theorem BlockReturns.permutation_step
    (allocated : Mutable.allocateTuple (row.map sequenceValue) heap = some (.ok tuple, middle))
    (rest : BlockReturns (globals := globals) module (setLocal env name tuple)
      (body ++ [Calls.loopContinuation body (.permutationStepLoop name remaining body otherwise)] ++ following)
      middle answer finalHeap) :
    BlockReturns (globals := globals) module env
      (.permutationStepLoop name (row :: remaining) body otherwise :: following) heap answer finalHeap :=
  fun anchors stack => .next (by simp [step, run, allocated]) (rest anchors stack)

theorem BlockReturns.permutation_done
    (rest : BlockReturns (globals := globals) module env (otherwise ++ following) heap answer finalHeap) :
    BlockReturns (globals := globals) module env
      (.permutationStepLoop name [] body otherwise :: following) heap answer finalHeap :=
  fun anchors stack => .next rfl (rest anchors stack)

theorem BlockContinues.for_permutations
    (arguments : Evaluates.Arguments (globals := globals) module env expressions heap values middle)
    (captured : permutationRows values middle = some (.ok rows, middle))
    (executed : BlockContinues (globals := globals) module env
      [.permutationStepLoop (comprehensionTargetName target) rows
        (comprehensionTargetBody target body) otherwise] middle finalEnv finalHeap) :
    BlockContinues (globals := globals) module env
      [.forIn target (.permutationsIterable expressions) body otherwise] heap finalEnv finalHeap := by
  intro following anchors stack
  exact .next rfl ((Evaluates.arguments_reach arguments _ [] anchors stack).trans
    (.next (by simp [step, run, captured]) (executed following anchors stack)))

theorem BlockContinues.permutation_step
    (allocated : Mutable.allocateTuple (row.map sequenceValue) heap = some (.ok tuple, middle))
    (executed : BlockContinues (globals := globals) module (setLocal env name tuple)
      (body ++ [Calls.loopContinuation body (.permutationStepLoop name remaining body otherwise)])
      middle finalEnv finalHeap) :
    BlockContinues (globals := globals) module env
      [.permutationStepLoop name (row :: remaining) body otherwise] heap finalEnv finalHeap :=
  fun following anchors stack =>
    .next (by simp [step, run, allocated, List.append_assoc]) (executed following anchors stack)

theorem BlockContinues.permutation_done
    (executed : BlockContinues (globals := globals) module env otherwise heap finalEnv finalHeap) :
    BlockContinues (globals := globals) module env
      [.permutationStepLoop name [] body otherwise] heap finalEnv finalHeap :=
  fun following anchors stack => .next rfl (executed following anchors stack)

theorem Evaluates.list_comp_targets_permutations
    (arguments : Arguments (globals := globals) module env expressions heap values middle)
    (captured : permutationRows values middle = some (.ok rows, middle))
    (executed : BlockContinues (globals := globals) module
      (comprehensionTargetsEnv env ((target, .permutationsIterable expressions, filters) :: generators))
      [.permutationStepLoop (comprehensionTargetName target) rows
        (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody [.comprehensionAppend middle.length element] generators))) []]
      (middle ++ [.list []]) finalEnv finalHeap) :
    Evaluates (globals := globals) module env
      (.listCompTargets element ((target, .permutationsIterable expressions, filters) :: generators))
      heap (.ref middle.length) finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (arguments_reach arguments _ [] anchors stack).trans
  exact .next (by simp [step, comprehensionTargetsStart, run, captured])
    ((executed [] anchors (.comprehensionResult middle.length :: stack)).trans
      (.next rfl (.next rfl .refl)))

theorem GeneratorCollects.permutations
    (arguments : Evaluates.Arguments (globals := globals) module env expressions heap values middle)
    (captured : permutationRows values middle = some (.ok rows, middle))
    (executed : BlockContinues (globals := globals) module
      (comprehensionTargetsEnv env ((target, .permutationsIterable expressions, filters) :: generators))
      [.permutationStepLoop (comprehensionTargetName target) rows
        (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody [.comprehensionAppend middle.length element] generators))) []]
      (middle ++ [.list []]) finalEnv collectedHeap)
    (finished : GeneratorFinishes action collectedHeap middle.length value finalHeap) :
    GeneratorCollects (globals := globals) module action element
      ((target, .permutationsIterable expressions, filters) :: generators) env heap value finalHeap := by
  intro anchors stack
  apply (Evaluates.arguments_reach arguments _ [] anchors stack).trans
  exact .next (by simp [step, comprehensionTargetsStart, run, captured])
    ((executed [] anchors (.comprehensionResult middle.length :: .generatorEnd :: .generatorConsumer action :: stack)).trans
      (.next rfl (.next rfl (.next rfl (finished.reaches anchors stack)))))

end FormalSW.PyAst.HeapCalls
