import lang.py.FormalSW.HeapCalls

/-! Nested name targets reuse flat unpacking and ordered assignments. The source
step retains the caller's heap, continuation, and following statements. -/
namespace FormalSW.PyAst.HeapCalls
variable {globals : Mutable.Globals}

/-- Compose a proof of the lowered assignments with the original nested target. -/
theorem BlockContinues.unpack_nested (asList : Bool)
    (nested : Calls.targetNames targets = none)
    (lowered : BlockContinues (globals := globals) module env
      (UnpackingTargets.assignment targets expression) heap finalEnv finalHeap) :
    BlockContinues (globals := globals) module env
      [.assign [if asList then .list targets else .tuple targets] expression]
      heap finalEnv finalHeap := by
  intro following anchors stack
  refine .next (following := ⟨.block (UnpackingTargets.assignment targets expression ++ following) env,
    stack, heap⟩) ?_ (lowered following anchors stack)
  cases asList <;> simp [step, nested]

/-- Returning blocks can use the same lowering without changing their suffix. -/
theorem BlockReturns.unpack_nested (asList : Bool)
    (nested : Calls.targetNames targets = none)
    (lowered : BlockReturns (globals := globals) module env
      (UnpackingTargets.assignment targets expression ++ following) heap answer finalHeap) :
    BlockReturns (globals := globals) module env
      (.assign [if asList then .list targets else .tuple targets] expression :: following)
      heap answer finalHeap := by
  intro anchors stack
  refine .next (following := ⟨.block (UnpackingTargets.assignment targets expression ++ following) env,
    stack, heap⟩) ?_ (lowered anchors stack)
  cases asList <;> simp [step, nested]

end FormalSW.PyAst.HeapCalls
