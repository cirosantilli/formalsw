import lang.py.FormalSW.SetRuntimeCost

namespace FormalSW.PyAst.SetCalls.Runtime

theorem advance
    (transition : step (globals := globals) module anchors choices initial = .next following)
    (measured : charge arithmetic module initial = some amount)
    (unchanged : following.core.heap = initial.core.heap) :
    Reaches (globals := globals) arithmetic module anchors choices initial amount following := by
  apply RuntimeCost.Amortized.Reaches.next
    (step := fun state => step (globals := globals) module anchors choices state)
    (charge := fun state => charge arithmetic module state) transition measured
  simp only [potential, HeapCalls.Runtime.potential, unchanged]
  omega

/-- Capture representatives once; the source set remains live for mutation checks. -/
theorem acquire (found : heap[address]? = some (.set items)) :
    Reaches (globals := globals) arithmetic module anchors choices
      ⟨⟨.value (.ref address), .sequence name body otherwise following env :: stack, heap⟩, used⟩
      (items.length + 2)
      ⟨⟨.block (.setStepLoop name address items items body otherwise :: following) env,
        stack, heap⟩, used⟩ := by
  apply advance
  · simp [step, HeapCalls.step, HeapCalls.run, HeapCalls.protectGenerator,
      Mutable.sequence, Mutable.unsupported, found, iteratorStep]
  · simp [charge, HeapCalls.Runtime.charge, iteratorCharge, found]
  · rfl

/-- Exhaustion checks the source size and leaves the schedule unchanged. -/
theorem iterator_done (found : heap[address]? = some (.set current))
    (sameSize : current.length = original.length) :
    Reaches (globals := globals) .word module anchors choices
      ⟨⟨.block (.setStepLoop name address original [] body otherwise :: following) env,
        stack, heap⟩, used⟩ 5
      ⟨⟨.block (otherwise ++ following) env, stack, heap⟩, used⟩ := by
  apply advance
  · simp [step, HeapCalls.step, iteratorStep, found, sameSize]
  · simp [charge, HeapCalls.Runtime.charge, iteratorCharge, found, PrimitiveWork.integer]
  · rfl

/-- Every schedule may select any remaining representative; the cost is uniform
in that choice and also includes the live-size check. -/
theorem iterator_step (found : heap[address]? = some (.set current))
    (sameSize : current.length = original.length)
    (nonempty : remaining ≠ [])
    (selected : remaining[choices used % remaining.length]? = some item) :
    Reaches (globals := globals) .word module anchors choices
      ⟨⟨.block (.setStepLoop name address original remaining body otherwise :: following) env,
        stack, heap⟩, used⟩ (remaining.length + 5)
      ⟨⟨.block (body ++ [Calls.loopContinuation body
          (.setStepLoop name address original (remaining.eraseIdx (choices used % remaining.length))
            body otherwise)] ++ following)
          (HeapCalls.setLocal env name (.scalar item)), stack, heap⟩, used + 1⟩ := by
  apply advance
  · cases remaining with
    | nil => contradiction
    | cons head tail =>
        simp only [List.length_cons] at selected
        simp [step, HeapCalls.step, iteratorStep, found, sameSize, selected]
  · simp [charge, HeapCalls.Runtime.charge, iteratorCharge, found, PrimitiveWork.integer,
      Nat.add_assoc]
  · rfl

end FormalSW.PyAst.SetCalls.Runtime
