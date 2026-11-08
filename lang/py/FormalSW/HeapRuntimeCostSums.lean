import lang.py.FormalSW.HeapRuntimeCostSumGenerators

namespace FormalSW.PyAst.HeapCalls.Runtime

/-- Sum a suffix of an integer list, charging every read, addition and loop guard. -/
theorem sum_list_loop (values remaining : List Int) (position : Nat)
    (found : heap[address]? = some (.list (values.map (fun n => .scalar (.int n)))))
    (suffix : values.drop position = remaining)
    (accumulator : env sumAccumulator = some (.scalar (.int initial))) :
    BlockReturnsIn .word module env
      [.sequenceStepLoop sumItem (.ref address) position (sumBody (.name sumItem) []) [],
        .return (.name sumAccumulator)] heap (13*remaining.length+7)
      (.scalar (.int (remaining.foldl Int.add initial))) heap := by
  exact sum_sequence_loop (values := values) (encode := fun n => .scalar (.int n))
    (number := id) remaining position 1 (by decide)
    (by simp [sequenceValue, Mutable.sequence, found])
    (by intro name position body otherwise following env stack; simp [charge, found, PrimitiveWork.integer])
    (fun _ _ lookup => EvaluatesIn.lookup lookup) suffix accumulator

/-- Ordinary sum arguments finish evaluating before iteration starts. -/
theorem EvaluatesIn.sum_list {values : List Int}
    (iterated : EvaluatesIn .word module env iterable heap ca (.ref address) middle)
    (started : EvaluatesIn .word module env start middle cb (.scalar (.int initial)) afterStart)
    (found : afterStart[address]? = some (.list (values.map (fun n => .scalar (.int n))))) :
    EvaluatesIn .word module env (.sumSequence iterable start) heap
      (ca+cb+13*values.length+14) (.scalar (.int (values.foldl Int.add initial))) afterStart := by
  intro anchors stack
  have first : Reaches .word module anchors
      ⟨.expr (.sumSequence iterable start) env, stack, heap⟩ 1
      (argumentsState .sumSequence env [] [iterable, start] stack heap) := advance rfl rfl rfl
  have arguments := (ArgumentsIn.cons iterated (ArgumentsIn.cons started ArgumentsIn.nil)).reaches
    (completed := []) .sumSequence anchors stack
  have enter : Reaches .word module anchors
      ⟨.operation .sumSequence [.ref address, .scalar (.int initial)], stack, afterStart⟩ 3
      ⟨.block [.sequenceStepLoop sumItem (.ref address) 0 (sumBody (.name sumItem) []) [],
          .return (.name sumAccumulator)]
        (setLocal (fun _ => none) sumAccumulator (.scalar (.int initial))), stack, afterStart⟩ :=
    advance (by simp [step, sumSequenceStart, run, Mutable.sequence, found, sumEnter, sumInitial, sequenceSource])
      (by simp [charge, operation, sequenceLength, found, PrimitiveWork.integer]) rfl
  have loop := sum_list_loop (module := module) (initial := initial) values values 0 found rfl
    (env := setLocal (fun _ => none) sumAccumulator (.scalar (.int initial))) (by simp [setLocal])
  exact (((first.trans arguments).trans enter).trans (loop anchors stack)).mono (by simp; omega)

end FormalSW.PyAst.HeapCalls.Runtime
