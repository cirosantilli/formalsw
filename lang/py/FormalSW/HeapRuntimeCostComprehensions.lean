import lang.py.FormalSW.HeapRuntimeCostSequences

/-! Comprehensions pay for acquisition, each emitted element, dynamic-array
resizing, and zip tuple construction. Element effects precede the append. -/
namespace FormalSW.PyAst.HeapCalls.Runtime
variable {globals : Mutable.Globals}
open PrimitiveWork

theorem BlockContinuesIn.comprehension_append
    (evaluated : EvaluatesIn (globals := globals) arithmetic module env expression heap cost value middle)
    (found : middle[address]? = some (.list items)) :
    BlockContinuesIn (globals := globals) arithmetic module env [.comprehensionAppend address expression] heap
      (cost+7) env (middle.set address (.list (items ++ [value]))) := by
  intro following anchors stack
  have first : Reaches (globals := globals) arithmetic module anchors
      ⟨.block ([.comprehensionAppend address expression] ++ following) env, stack, heap⟩ 1
      ⟨.expr expression env, .arguments (.append address) [] [] env :: .discard following env :: stack, heap⟩ :=
    advance rfl rfl rfl
  have ready : Reaches (globals := globals) arithmetic module anchors
      ⟨.value value, .arguments (.append address) [] [] env :: .discard following env :: stack, middle⟩ 1
      ⟨.operation (.append address) [value], .discard following env :: stack, middle⟩ := advance rfl rfl rfl
  have emitted := append_operation (globals := globals) (arithmetic := arithmetic) (module := module)
    (anchors := anchors) (stack := .discard following env :: stack) middle address items value found
  have last : Reaches (globals := globals) arithmetic module anchors
      ⟨.value (.scalar .none), .discard following env :: stack, middle.set address (.list (items ++ [value]))⟩ 1
      ⟨.block following env, stack, middle.set address (.list (items ++ [value]))⟩ := advance rfl rfl rfl
  exact ((((first.trans (evaluated anchors _)).trans ready).trans emitted).trans last).mono (by omega)

theorem EvaluatesIn.list_comp_range
    (arguments : ArgumentsIn (globals := globals) arithmetic module env 0 expressions heap ca values middle)
    (bounds : rangeBounds values = .ok (start, stop, stride))
    (priced : operation arithmetic middle
      (.comprehension element ((name, .call (.name "range") expressions, filters) :: generators)
        (comprehensionEnv env ((name, .call (.name "range") expressions, filters) :: generators))) values = some work)
    (executed : BlockContinuesIn (globals := globals) arithmetic module
      (comprehensionEnv env ((name, .call (.name "range") expressions, filters) :: generators))
      [.rangeStepLoop name start stop stride
        (comprehensionFilters filters (comprehensionBody middle.length element generators)) []]
      (middle ++ [.list []]) cb finalEnv finalHeap) :
    EvaluatesIn (globals := globals) arithmetic module env
      (.listComp element ((name, .call (.name "range") expressions, filters) :: generators))
      heap (ca+work+cb+4) (.ref middle.length) finalHeap := by
  intro anchors stack
  let localEnv := comprehensionEnv env ((name, .call (.name "range") expressions, filters) :: generators)
  let op := Operation.comprehension element ((name, .call (.name "range") expressions, filters) :: generators) localEnv
  have first : Reaches (globals := globals) arithmetic module anchors
      ⟨.expr (.listComp element ((name, .call (.name "range") expressions, filters) :: generators)) env, stack, heap⟩ 1
      (argumentsState op env [] expressions stack heap) := advance rfl rfl (by cases expressions <;> rfl)
  have args := arguments.reaches (completed := []) op anchors stack
  have setup : Reaches (globals := globals) arithmetic module anchors ⟨.operation op values, stack, middle⟩ (work+1)
      ⟨.block [.rangeStepLoop name start stop stride
        (comprehensionFilters filters (comprehensionBody middle.length element generators)) []] localEnv,
        .comprehensionResult middle.length :: stack, middle ++ [.list []]⟩ := by
    apply RuntimeCost.Amortized.Reaches.next (amount := work+1)
    · simp [step, op, comprehensionStart, bounds]
    · simp [charge, op, localEnv, priced]
    · simp [potential, heapPotential_allocate, DynamicArray.potential, DynamicArray.capacity]
  have finish : Reaches (globals := globals) arithmetic module anchors
      ⟨.block [] finalEnv, .comprehensionResult middle.length :: stack, finalHeap⟩ 2
      ⟨.value (.ref middle.length), stack, finalHeap⟩ := by
    exact (advance rfl rfl rfl : Reaches (globals := globals) arithmetic module anchors
      ⟨.block [] finalEnv, .comprehensionResult middle.length :: stack, finalHeap⟩ 1
      ⟨.value (.scalar .none), .comprehensionResult middle.length :: stack, finalHeap⟩).trans
        (advance rfl rfl rfl)
  exact ((((first.trans args).trans setup).trans (executed [] anchors _)).trans finish).mono (by omega)

/-- Ordinary builtin sequences retain their receiver after iterable evaluation.
The loop charges reads and output appends separately. -/
theorem EvaluatesIn.list_comp_sequence
    (ordinary : ∀ expressions, iterable ≠ .call (.name "range") expressions)
    (evaluated : EvaluatesIn (globals := globals) arithmetic module env iterable heap ca value middle)
    (sequence : Mutable.sequence value middle = some (.ok items, middle))
    (length : sequenceLength middle value = some size)
    (executed : BlockContinuesIn (globals := globals) arithmetic module
      (comprehensionEnv env ((name, iterable, filters) :: generators))
      [.sequenceStepLoop name (sequenceSource value) 0
        (comprehensionFilters filters (comprehensionBody middle.length element generators)) []]
      (middle ++ [.list []]) cb finalEnv finalHeap) :
    EvaluatesIn (globals := globals) arithmetic module env (.listComp element ((name, iterable, filters) :: generators))
      heap (ca+cb+7) (.ref middle.length) finalHeap := by
  intro anchors stack
  let localEnv := comprehensionEnv env ((name, iterable, filters) :: generators)
  let op := Operation.comprehension element ((name, iterable, filters) :: generators) localEnv
  have first : Reaches (globals := globals) arithmetic module anchors
      ⟨.expr (.listComp element ((name, iterable, filters) :: generators)) env, stack, heap⟩ 1
      (argumentsState op env [] [iterable] stack heap) :=
    advance (by cases iterable <;> simp_all [step, op, localEnv]) rfl rfl
  have args := (ArgumentsIn.cons evaluated ArgumentsIn.nil).reaches (completed := []) op anchors stack
  have setup : Reaches (globals := globals) arithmetic module anchors ⟨.operation op [value], stack, middle⟩ 3
      ⟨.block [.sequenceStepLoop name (sequenceSource value) 0
        (comprehensionFilters filters (comprehensionBody middle.length element generators)) []] localEnv,
        .comprehensionResult middle.length :: stack, middle ++ [.list []]⟩ := by
    apply RuntimeCost.Amortized.Reaches.next (amount := 3)
    · cases iterable <;> simp_all [step, op, comprehensionStart, run]
    · cases iterable <;> simp_all [charge, op, operation]
    · simp [potential, heapPotential_allocate, DynamicArray.potential, DynamicArray.capacity]
  have finish : Reaches (globals := globals) arithmetic module anchors
      ⟨.block [] finalEnv, .comprehensionResult middle.length :: stack, finalHeap⟩ 2
      ⟨.value (.ref middle.length), stack, finalHeap⟩ := by
    exact (advance rfl rfl rfl : Reaches (globals := globals) arithmetic module anchors
      ⟨.block [] finalEnv, .comprehensionResult middle.length :: stack, finalHeap⟩ 1
      ⟨.value (.scalar .none), .comprehensionResult middle.length :: stack, finalHeap⟩).trans
        (advance rfl rfl rfl)
  exact ((((first.trans args).trans setup).trans (executed [] anchors _)).trans finish).mono (by simp; omega)

theorem BlockContinuesIn.zip_step
    (fetched : zipItem sources position heap = some (.ok (some fields), heap))
    (allocated : Mutable.allocateTuple fields heap = some (.ok (.ref heap.length), heap ++ [.tuple fields]))
    (priced : zipIteration arithmetic heap sources position = some work)
    (rest : BlockContinuesIn (globals := globals) arithmetic module (setLocal env name (.ref heap.length))
      (body ++ [Calls.loopContinuation body (.zipStepLoop name sources (position+1) body otherwise)])
      (heap ++ [.tuple fields]) budget finalEnv finalHeap) :
    BlockContinuesIn (globals := globals) arithmetic module env [.zipStepLoop name sources position body otherwise]
      heap (work+budget) finalEnv finalHeap := by
  intro following anchors stack
  have first : Reaches (globals := globals) arithmetic module anchors
      ⟨.block ([.zipStepLoop name sources position body otherwise] ++ following) env, stack, heap⟩ work
      ⟨.block ((body ++ [Calls.loopContinuation body (.zipStepLoop name sources (position+1) body otherwise)]) ++ following)
        (setLocal env name (.ref heap.length)), stack, heap ++ [.tuple fields]⟩ := by
    apply RuntimeCost.Amortized.Reaches.next (amount := work)
    · simp [step, run, fetched, allocated, List.append_assoc]
    · simp [charge, priced]
    · simp [potential, heapPotential, objectPotential]
  exact first.trans (rest following anchors stack)

theorem BlockContinuesIn.zip_done
    (finished : zipItem sources position heap = some (.ok none, heap))
    (priced : zipIteration arithmetic heap sources position = some work)
    (rest : BlockContinuesIn (globals := globals) arithmetic module env otherwise heap budget finalEnv finalHeap) :
    BlockContinuesIn (globals := globals) arithmetic module env [.zipStepLoop name sources position body otherwise]
      heap (work+budget) finalEnv finalHeap := by
  intro following anchors stack
  have first : Reaches (globals := globals) arithmetic module anchors
      ⟨.block ([.zipStepLoop name sources position body otherwise] ++ following) env, stack, heap⟩ work
      ⟨.block (otherwise ++ following) env, stack, heap⟩ :=
    advance (by simp [step, run, finished]) (by simp [charge, priced]) rfl
  exact first.trans (rest following anchors stack)

theorem EvaluatesIn.list_comp_zip
    (arguments : ArgumentsIn (globals := globals) arithmetic module env 0 expressions heap ca values middle)
    (acquired : zipSources values middle = some (.ok sources, middle))
    (priced : operation arithmetic middle
      (.comprehensionTargets element ((target, .zipIterable expressions, filters) :: generators)
        (comprehensionTargetsEnv env ((target, .zipIterable expressions, filters) :: generators))) values = some work)
    (executed : BlockContinuesIn (globals := globals) arithmetic module
      (comprehensionTargetsEnv env ((target, .zipIterable expressions, filters) :: generators))
      [.zipStepLoop (comprehensionTargetName target) sources 0
        (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody [.comprehensionAppend middle.length element] generators))) []]
      (middle ++ [.list []]) cb finalEnv finalHeap) :
    EvaluatesIn (globals := globals) arithmetic module env
      (.listCompTargets element ((target, .zipIterable expressions, filters) :: generators))
      heap (ca+work+cb+4) (.ref middle.length) finalHeap := by
  intro anchors stack
  let localEnv := comprehensionTargetsEnv env ((target, .zipIterable expressions, filters) :: generators)
  let op := Operation.comprehensionTargets element ((target, .zipIterable expressions, filters) :: generators) localEnv
  have first : Reaches (globals := globals) arithmetic module anchors
      ⟨.expr (.listCompTargets element ((target, .zipIterable expressions, filters) :: generators)) env, stack, heap⟩ 1
      (argumentsState op env [] expressions stack heap) := advance rfl rfl (by cases expressions <;> rfl)
  have args := arguments.reaches (completed := []) op anchors stack
  have setup : Reaches (globals := globals) arithmetic module anchors ⟨.operation op values, stack, middle⟩ (work+1)
      ⟨.block [.zipStepLoop (comprehensionTargetName target) sources 0
        (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody [.comprehensionAppend middle.length element] generators))) []] localEnv,
        .comprehensionResult middle.length :: stack, middle ++ [.list []]⟩ := by
    apply RuntimeCost.Amortized.Reaches.next (amount := work+1)
    · simp [step, op, comprehensionTargetsStart, acquired, run]
    · simp [charge, op, localEnv, priced]
    · simp [potential, heapPotential_allocate, DynamicArray.potential, DynamicArray.capacity]
  have finish : Reaches (globals := globals) arithmetic module anchors
      ⟨.block [] finalEnv, .comprehensionResult middle.length :: stack, finalHeap⟩ 2
      ⟨.value (.ref middle.length), stack, finalHeap⟩ := by
    exact (advance rfl rfl rfl : Reaches (globals := globals) arithmetic module anchors
      ⟨.block [] finalEnv, .comprehensionResult middle.length :: stack, finalHeap⟩ 1
      ⟨.value (.scalar .none), .comprehensionResult middle.length :: stack, finalHeap⟩).trans
        (advance rfl rfl rfl)
  exact ((((first.trans args).trans setup).trans (executed [] anchors _)).trans finish).mono (by omega)

theorem BlockContinuesIn.unpack_tuple
    (targetsValid : Calls.targetNames targets = some names)
    (evaluated : EvaluatesIn (globals := globals) arithmetic module env expression heap cost (.ref address) middle)
    (found : middle[address]? = some (.tuple items)) (arity : names.length = items.length) :
    BlockContinuesIn (globals := globals) arithmetic module env [.assign [.tuple targets] expression] heap
      (cost + targets.length + items.length + names.length + 2)
      (assignNames env names items) middle := by
  intro following anchors stack
  have first : Reaches (globals := globals) arithmetic module anchors
      ⟨.block ([.assign [.tuple targets] expression] ++ following) env, stack, heap⟩ (targets.length+1)
      ⟨.expr expression env, .unpack names following env :: stack, heap⟩ :=
    advance (by simp [step, targetsValid]) (by simp [charge, targetsValid]) rfl
  have assigned : Reaches (globals := globals) arithmetic module anchors
      ⟨.value (.ref address), .unpack names following env :: stack, middle⟩ (items.length+names.length+1)
      ⟨.block following (assignNames env names items), stack, middle⟩ :=
    advance (by simp [step, run, Mutable.sequence, found, arity])
      (by simp [charge, sequenceLength, found]) rfl
  exact ((first.trans (evaluated anchors _)).trans assigned).mono (by omega)

end FormalSW.PyAst.HeapCalls.Runtime
