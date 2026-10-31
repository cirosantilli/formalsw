import lang.py.FormalSW.CoreFrame
import lang.py.FormalSW.SetCalls

/-! Set traversal preserves private cells for every choice schedule, including fallback after unsupported core steps. -/
namespace FormalSW.PyAst.SetCalls.Framing
open Mutable Mutable.Relocation HeapCalls
set_option Elab.async false

def RetainsCell (address : Nat) (object : Object) : Step State Mutable.Completion → Prop
  | .next state => SavedCell address object state.core.heap
  | .done (.ok completion) => SavedCell address object completion.heap
  | .done (.error _) | .unsupported => True

theorem liftStep_retains_cell (address used : Nat) (object : Object)
    (transition : Step HeapCalls.State Mutable.Completion)
    (retained : HeapCalls.Framing.RetainsCell address object transition) :
    RetainsCell address object (liftStep used transition) := by
  cases transition with
  | next | unsupported => exact retained
  | done outcome => cases outcome <;> exact retained

theorem iteratorStep_cell (address anchors : Nat) (object : Object) (state : State)
    (choices : ChoiceSchedule) (globals : Globals) (saved : SavedCell address object state.core.heap) :
    RetainsCell address object (iteratorStep choices anchors state globals) := by
  rcases state with ⟨⟨work, stack, heap⟩, used⟩
  simp only [iteratorStep, comprehensionStart, sumEnter]
  with_reducible repeat' first
    | exact saved
    | trivial
    | apply liftStep_retains_cell
    | (solve | simp only [RetainsCell, HeapCalls.Framing.RetainsCell, done] <;> first
        | assumption
        | exact SavedCell.append address object _ _ saved)
    | apply HeapCalls.Framing.run_retains_cell _ _ _ _ _ _ _ saved
    | exact Heapq.preserves_sumInitial _ _
    | intro result after retained
    | exact retained
    | (solve | simp only [HeapCalls.Framing.RetainsCell] <;> assumption)
    | split

theorem step_cell (module : Module) (address anchors : Nat) (object : Object) (state : State)
    (choices : ChoiceSchedule) (globals : Globals)
    (separate : HeapCalls.Framing.StateSeparate address state.core)
    (saved : SavedCell address object state.core.heap) :
    RetainsCell address object (step module anchors choices state globals) := by
  have retained := HeapCalls.Framing.step_cell module address anchors object state.core globals separate saved
  unfold step
  cases transition : HeapCalls.step module anchors state.core globals with
  | unsupported => exact iteratorStep_cell address anchors object state choices globals saved
  | next following => exact liftStep_retains_cell address state.choicesUsed object _ (by simpa only [transition] using retained)
  | done outcome => exact liftStep_retains_cell address state.choicesUsed object _ (by simpa only [transition] using retained)

end FormalSW.PyAst.SetCalls.Framing
