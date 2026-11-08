import lang.py.FormalSW.HeapRuntimeCostControl

/-! Runtime proofs can reuse an independently proved functional result without
repeating its invariants. Both proofs must describe the same source execution. -/
namespace FormalSW.PyAst.HeapCalls.Runtime
variable {globals : Mutable.Globals}

private theorem trace_reaches
    (trace : RuntimeCost.Reaches (step (globals := globals) module anchors)
      (charge arithmetic module) initial cost final) :
    HeapCalls.Reaches (globals := globals) module anchors initial final := by
  induction trace with
  | refl => exact .refl
  | next transition _ _ ih => exact .next transition ih

theorem ReturnsIn.returnsValue
    (run : ReturnsIn (globals := globals) arithmetic module name values heap budget value finalHeap) :
    ReturnsValue (globals := globals) module name values heap value finalHeap := by
  intro anchors stack
  obtain ⟨cost, trace, _⟩ := run anchors stack
  exact trace_reaches trace

theorem ReturnsIn.result_unique
    (run : ReturnsIn (globals := globals) arithmetic module name values heap budget value finalHeap)
    (correct : ReturnsValue (globals := globals) module name values heap expected expectedHeap) :
    value = expected ∧ finalHeap = expectedHeap := by
  have same := run.returnsValue.finishes.unique correct.finishes
  have completionSame := Except.ok.inj same
  have heapSame := congrArg Mutable.Completion.heap completionSame
  have resultSame := congrArg Mutable.Completion.outcome completionSame
  exact ⟨Except.ok.inj resultSame, heapSame⟩

theorem ReturnsIn.with_result
    (run : ReturnsIn (globals := globals) arithmetic module name values heap budget value finalHeap)
    (correct : ReturnsValue (globals := globals) module name values heap expected expectedHeap) :
    ReturnsIn (globals := globals) arithmetic module name values heap budget expected expectedHeap := by
  obtain ⟨rfl, rfl⟩ := run.result_unique correct
  exact run

end FormalSW.PyAst.HeapCalls.Runtime
