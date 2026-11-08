import lang.py.FormalSW.HeapRuntimeCostComprehensions
import lang.py.FormalSW.HeapRuntimeCostSets

/-! Range-based scalar-set comprehensions. Iterator acquisition and the empty
collector are charged once; the supplied loop pays for filters, element
evaluation and each collision-chain insertion into the live collector. -/
namespace FormalSW.PyAst.HeapCalls.Runtime
variable {globals : Mutable.Globals}

/-- Evaluate the element first, then inspect and update the live set. Duplicate
keys retain the existing representative but still incur the insertion tariff. -/
theorem BlockContinuesIn.comprehension_add
    (evaluated : EvaluatesIn (globals := globals) arithmetic module env expression heap cost (.scalar value) middle)
    (found : middle[address]? = some (.set items)) :
    BlockContinuesIn (globals := globals) arithmetic module env [.comprehensionAdd address expression] heap
      (cost + SetWork.insert .collisionChain arithmetic items value + 4) env
      (middle.set address (.set (ScalarSet.insert items value))) := by
  intro following anchors stack
  have first : Reaches (globals := globals) arithmetic module anchors
      ⟨.block ([.comprehensionAdd address expression] ++ following) env, stack, heap⟩ 1
      ⟨.expr expression env, .arguments (.add address) [] [] env :: .discard following env :: stack, heap⟩ :=
    advance rfl rfl rfl
  have ready : Reaches (globals := globals) arithmetic module anchors
      ⟨.value (.scalar value), .arguments (.add address) [] [] env :: .discard following env :: stack, middle⟩ 1
      ⟨.operation (.add address) [.scalar value], .discard following env :: stack, middle⟩ :=
    advance rfl rfl rfl
  have inserted : Reaches (globals := globals) arithmetic module anchors
      ⟨.operation (.add address) [.scalar value], .discard following env :: stack, middle⟩
      (SetWork.insert .collisionChain arithmetic items value + 1)
      ⟨.value (.scalar .none), .discard following env :: stack,
        middle.set address (.set (ScalarSet.insert items value))⟩ := by
    apply RuntimeCost.Amortized.Reaches.next
      (amount := SetWork.insert .collisionChain arithmetic items value + 1)
    · simp [step, result, run, primitive, Mutable.addItem, found, Except.map]
    · simp [charge, operation, SetWork.operation, found]
    · have unchanged := heapPotential_set middle address (.set items)
        (.set (ScalarSet.insert items value)) found
      simpa only [potential, objectPotential, Nat.add_zero] using
        Nat.add_le_add_left (Nat.le_of_eq unchanged)
          (SetWork.insert .collisionChain arithmetic items value + 1)
  have finish : Reaches (globals := globals) arithmetic module anchors
      ⟨.value (.scalar .none), .discard following env :: stack,
        middle.set address (.set (ScalarSet.insert items value))⟩ 1
      ⟨.block following env, stack, middle.set address (.set (ScalarSet.insert items value))⟩ :=
    advance rfl rfl rfl
  exact ((((first.trans (evaluated anchors _)).trans ready).trans inserted).trans finish).mono (by omega)

/-- The original range arguments run in the enclosing scope before allocating
the empty set. Filters, unpacking and any later generators execute in the
supplied loop and comprehension-local environment. -/
theorem EvaluatesIn.set_comp_range
    (arguments : ArgumentsIn (globals := globals) arithmetic module env 0 expressions heap ca values middle)
    (bounds : rangeBounds values = .ok (start, stop, stride))
    (priced : operation arithmetic middle
      (.setComprehension element ((target, .call (.name "range") expressions, filters) :: generators)
        (comprehensionTargetsEnv env ((target, .call (.name "range") expressions, filters) :: generators)))
      values = some work)
    (executed : BlockContinuesIn (globals := globals) arithmetic module
      (comprehensionTargetsEnv env ((target, .call (.name "range") expressions, filters) :: generators))
      [.rangeStepLoop (comprehensionTargetName target) start stop stride
        (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody [.comprehensionAdd middle.length element] generators))) []]
      (middle ++ [.set []]) cb finalEnv finalHeap) :
    EvaluatesIn (globals := globals) arithmetic module env
      (.setComp element ((target, .call (.name "range") expressions, filters) :: generators))
      heap (ca + work + cb + 4) (.ref middle.length) finalHeap := by
  intro anchors stack
  let localEnv := comprehensionTargetsEnv env ((target, .call (.name "range") expressions, filters) :: generators)
  let op := Operation.setComprehension element
    ((target, .call (.name "range") expressions, filters) :: generators) localEnv
  have first : Reaches (globals := globals) arithmetic module anchors
      ⟨.expr (.setComp element ((target, .call (.name "range") expressions, filters) :: generators)) env,
        stack, heap⟩ 1
      (argumentsState op env [] expressions stack heap) :=
    advance rfl rfl (by cases expressions <;> rfl)
  have args := arguments.reaches (completed := []) op anchors stack
  have setup : Reaches (globals := globals) arithmetic module anchors
      ⟨.operation op values, stack, middle⟩ (work + 1)
      ⟨.block [.rangeStepLoop (comprehensionTargetName target) start stop stride
        (comprehensionTargetBody target (comprehensionFilters filters
          (comprehensionTargetsBody [.comprehensionAdd middle.length element] generators))) []] localEnv,
        .comprehensionResult middle.length :: stack, middle ++ [.set []]⟩ := by
    apply RuntimeCost.Amortized.Reaches.next (amount := work + 1)
    · simp [step, op, comprehensionTargetsStart, bounds]
    · simp [charge, op, localEnv, priced]
    · simp [potential, heapPotential, objectPotential]
  have finish : Reaches (globals := globals) arithmetic module anchors
      ⟨.block [] finalEnv, .comprehensionResult middle.length :: stack, finalHeap⟩ 2
      ⟨.value (.ref middle.length), stack, finalHeap⟩ := by
    exact (advance rfl rfl rfl : Reaches (globals := globals) arithmetic module anchors
      ⟨.block [] finalEnv, .comprehensionResult middle.length :: stack, finalHeap⟩ 1
      ⟨.value (.scalar .none), .comprehensionResult middle.length :: stack, finalHeap⟩).trans
        (advance rfl rfl rfl)
  exact ((((first.trans args).trans setup).trans (executed [] anchors _)).trans finish).mono (by omega)

end FormalSW.PyAst.HeapCalls.Runtime
