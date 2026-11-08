import lang.py.FormalSW.HeapRuntimeCostListCopies

namespace FormalSW.PyAst.HeapCalls.Runtime
open PrimitiveWork

theorem EvaluatesIn.negate_int
    (argument : EvaluatesIn arithmetic module env expression heap cost (.scalar (.int number)) middle) :
    EvaluatesIn arithmetic module env (.unaryOp .uSub expression) heap
      (cost + integer arithmetic number + 2) (.scalar (.int (-number))) middle := by
  intro anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.expr (.unaryOp .uSub expression) env, stack, heap⟩ 1
      ⟨.expr expression env, .unary .uSub :: stack, heap⟩ := advance rfl rfl rfl
  have last : Reaches arithmetic module anchors
      ⟨.value (.scalar (.int number)), .unary .uSub :: stack, middle⟩ (integer arithmetic number+1)
      ⟨.value (.scalar (.int (-number))), stack, middle⟩ :=
    advance rfl rfl rfl
  exact ((first.trans (argument anchors _)).trans last).mono (by omega)

/-- Explicit stride bounds retain left-to-right evaluation and all bound effects. -/
theorem BlockReturnsIn.for_range_triple
    (left : EvaluatesIn .word module env a heap ca (.scalar (.int start)) middle)
    (right : EvaluatesIn .word module env b middle cb (.scalar (.int stop)) afterStop)
    (strideValue : EvaluatesIn .word module env c afterStop cc (.scalar (.int stride)) afterBounds)
    (nonzero : stride ≠ 0)
    (body : BlockReturnsIn .word module env (.rangeStepLoop name start stop stride loop otherwise :: following)
      afterBounds cost answer finalHeap) :
    BlockReturnsIn .word module env
      (.forIn (.name name) (.call (.name "range") [a,b,c]) loop otherwise :: following)
      heap (ca+cb+cc+cost+11) answer finalHeap := by
  intro anchors stack
  have first : Reaches .word module anchors
      ⟨.block (.forIn (.name name) (.call (.name "range") [a,b,c]) loop otherwise :: following) env, stack, heap⟩ 1
      ⟨.expr a env, .rangeArguments name [] [b,c] loop otherwise following env :: stack, heap⟩ := advance rfl rfl rfl
  have second : Reaches .word module anchors
      ⟨.value (.scalar (.int start)), .rangeArguments name [] [b,c] loop otherwise following env :: stack, middle⟩ 1
      ⟨.expr b env, .rangeArguments name [.scalar (.int start)] [c] loop otherwise following env :: stack, middle⟩ :=
    advance rfl rfl rfl
  have third : Reaches .word module anchors
      ⟨.value (.scalar (.int stop)), .rangeArguments name [.scalar (.int start)] [c] loop otherwise following env :: stack, afterStop⟩ 2
      ⟨.expr c env, .rangeArguments name [.scalar (.int start), .scalar (.int stop)] [] loop otherwise following env :: stack, afterStop⟩ :=
    advance rfl rfl rfl
  have ready : Reaches .word module anchors
      ⟨.value (.scalar (.int stride)), .rangeArguments name [.scalar (.int start), .scalar (.int stop)] [] loop otherwise following env :: stack, afterBounds⟩ 3
      ⟨.startRange name [.scalar (.int start), .scalar (.int stop), .scalar (.int stride)] loop otherwise following env, stack, afterBounds⟩ :=
    advance rfl rfl rfl
  have enter : Reaches .word module anchors
      ⟨.startRange name [.scalar (.int start), .scalar (.int stop), .scalar (.int stride)] loop otherwise following env, stack, afterBounds⟩ 4
      ⟨.block (.rangeStepLoop name start stop stride loop otherwise :: following) env, stack, afterBounds⟩ :=
    advance (by
      have evaluated : rangeBounds [.scalar (.int start), .scalar (.int stop), .scalar (.int stride)] =
          .ok (start, stop, stride) := by
        change (if stride = 0 then Except.error ({ typeName := "ValueError", args := [] } : ExceptionObject)
          else Except.ok (start, stop, stride)) = Except.ok (start, stop, stride)
        simp [nonzero]
      simp [step, evaluated]) rfl rfl
  exact ((((((((first.trans (left anchors _)).trans second).trans (right anchors _)).trans third).trans
    (strideValue anchors _)).trans ready).trans enter).trans (body anchors stack)).mono (by omega)

/-- Preserving the input prefix means its existing list credits cancel. -/
theorem ReturnsIn.timeBound_append
    (run : ReturnsIn arithmetic module name values heap budget value (heap ++ extra)) :
    TimeBound arithmetic module name values heap (budget+1) := by
  obtain ⟨cost, steps, paid⟩ := run heap.length []
  have terminal : RuntimeCost.Finishes (HeapCalls.step module heap.length) (charge arithmetic module)
      ⟨.value value, [], heap ++ extra⟩ 1 (.ok ⟨.ok value, [], heap ++ extra, heap.length⟩) := .done rfl rfl
  refine ⟨cost+1, _, steps.finishes terminal, ?_⟩
  simp only [potential, heapPotential, List.map_append, List.sum_append] at paid
  omega

end FormalSW.PyAst.HeapCalls.Runtime
