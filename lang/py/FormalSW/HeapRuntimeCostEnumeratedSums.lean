import lang.py.FormalSW.HeapRuntimeCostEnumeration

namespace FormalSW.PyAst.HeapCalls.Runtime

/-- Acquire the source and explicit enumeration start before entering the
generator, then charge every enumerated summand through the supplied loop. -/
theorem EvaluatesIn.sum_enumerate
    (arguments : ArgumentsIn .word module env 0 [iterable, counterExpression] heap ca
      [source, .scalar (.int counter)] middle)
    (sequence : Mutable.sequence source middle = some (.ok items, middle))
    (length : sequenceLength middle source = some size)
    (started : EvaluatesIn .word module env start middle cb (.scalar (.int initial)) afterStart)
    (loop : BlockReturnsIn .word module
      (setLocal (comprehensionTargetsEnv env
        [(.tuple [.name index, .name name], .call (.name "enumerate") [iterable, counterExpression], [])])
        sumAccumulator (.scalar (.int initial)))
      [.enumerateStepLoop index name (sequenceSource source) 0 counter (sumBody element []) [],
        .return (.name sumAccumulator)] afterStart budget answer finalHeap) :
    EvaluatesIn .word module env
      (.sumGeneratorTargets element
        [(.tuple [.name index, .name name], .call (.name "enumerate") [iterable, counterExpression], [])] start)
      heap (ca + cb + budget + 7) answer finalHeap := by
  let generators : List (Expr × Expr × List Expr) :=
    [(.tuple [.name index, .name name], .call (.name "enumerate") [iterable, counterExpression], [])]
  let op := Operation.sumGeneratorTargets element generators env start
  let localEnv := comprehensionTargetsEnv env generators
  let next := Stmt.enumerateStepLoop index name (sequenceSource source) 0 counter (sumBody element []) []
  intro anchors stack
  have first : Reaches .word module anchors
      ⟨.expr (.sumGeneratorTargets element generators start) env, stack, heap⟩ 1
      (argumentsState op env [] [iterable, counterExpression] stack heap) :=
    advance rfl rfl rfl
  have args := arguments.reaches (completed := []) op anchors stack
  have ready : Reaches .word module anchors
      ⟨.operation op [source, .scalar (.int counter)], stack, middle⟩ 3
      ⟨.expr start env, .sumStart next localEnv :: stack, middle⟩ :=
    advance (by simp [step, op, generators, sumGeneratorTargetsStart, itemsReceiver,
      enumerateTarget, enumerateStart, run, sequence, next, localEnv, comprehensionFilters,
      comprehensionTargetsBody])
      (by simp [charge, op, generators, operation, enumeratedGenerator, length, PrimitiveWork.integer]) rfl
  have enter : Reaches .word module anchors
      ⟨.value (.scalar (.int initial)), .sumStart next localEnv :: stack, afterStart⟩ 2
      ⟨.block [next, .return (.name sumAccumulator)]
        (setLocal localEnv sumAccumulator (.scalar (.int initial))), .generatorEnd :: stack, afterStart⟩ :=
    advance rfl rfl rfl
  have finish : Reaches .word module anchors
      ⟨.value answer, .generatorEnd :: stack, finalHeap⟩ 1 ⟨.value answer, stack, finalHeap⟩ :=
    advance rfl rfl rfl
  exact ((((((first.trans args).trans ready).trans (started anchors _)).trans enter).trans
    (loop anchors (.generatorEnd :: stack))).trans finish).mono (by omega)

end FormalSW.PyAst.HeapCalls.Runtime
