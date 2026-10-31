import lang.py.FormalSW.ExpressionFrame
import lang.py.FormalSW.WorkFrame
import lang.py.FormalSW.OperationFrame

/-! Complete core-interpreter frame rules, with separation only at actual write dispatch. -/
namespace FormalSW.PyAst.HeapCalls.Framing
open Mutable Mutable.Relocation
set_option Elab.async false

/-- Other work only reads, allocates, or schedules evaluation of a later operation. -/
def StateSeparate (address : Nat) (state : State) : Prop :=
  match state.work with
  | .operation operation values => ∀ receiver ∈ operationTargets operation values, receiver ≠ address
  | .value _ => ∀ frame ∈ state.stack.head?, FrameSeparate address frame
  | _ => True

theorem step_cell (module : Module) (address anchors : Nat) (object : Object)
    (state : State) (globals : Globals) (separate : StateSeparate address state)
    (saved : SavedCell address object state.heap) :
    RetainsCell address object (step module anchors state globals) := by
  rcases state with ⟨work, stack, heap⟩
  cases work with
  | sortedLoop => apply step_sortedLoop_cell <;> assumption
  | extremumLoop => apply step_extremumLoop_cell <;> assumption
  | dictionary => apply step_dictionary_cell <;> assumption
  | startRange => apply step_startRange_cell <;> assumption
  | operation => apply step_operation_cell <;> assumption
  | expr => apply step_expression_cell <;> assumption
  | block => apply step_block_cell <;> assumption
  | value => apply step_value_cell <;> assumption

/-- A finite prefix retains the cell if every reached write has a separate receiver. -/
theorem reaches_cell (module : Module) (address anchors : Nat) (object : Object)
    (initial final : State) (globals : Globals)
    (path : Reaches module anchors initial final globals)
    (separate : ∀ state, Reaches module anchors initial state globals → StateSeparate address state)
    (saved : SavedCell address object initial.heap) : SavedCell address object final.heap := by
  induction path with
  | refl => exact saved
  | @next state following final globals transition path ih =>
    apply ih
    · intro state reached
      exact separate state (.next transition reached)
    · have retained := step_cell module address anchors object state globals (separate state .refl) saved
      simpa only [transition, RetainsCell] using retained

theorem finishes_retains_cell (module : Module) (address anchors : Nat) (object : Object)
    (initial : State) (globals : Globals) (outcome : Except ExceptionObject Completion)
    (finished : Finishes (step module anchors · globals) initial outcome)
    (separate : ∀ state, Reaches module anchors initial state globals → StateSeparate address state)
    (saved : SavedCell address object initial.heap) : RetainsCell address object (.done outcome) := by
  induction finished with
  | @done state outcome transition =>
    have retained := step_cell module address anchors object state globals (separate state .refl) saved
    simpa only [transition] using retained
  | @next state following outcome transition rest ih =>
    apply ih
    · intro state reached
      exact separate state (.next transition reached)
    · have retained := step_cell module address anchors object state globals (separate state .refl) saved
      simpa only [transition, RetainsCell] using retained

/-- Both successful returns and Python exceptions retain the cell in their completion heap. -/
theorem finishes_cell (module : Module) (address anchors : Nat) (object : Object)
    (initial : State) (globals : Globals) (completion : Completion)
    (finished : Finishes (step module anchors · globals) initial (.ok completion))
    (separate : ∀ state, Reaches module anchors initial state globals → StateSeparate address state)
    (saved : SavedCell address object initial.heap) : SavedCell address object completion.heap :=
  finishes_retains_cell module address anchors object initial globals (.ok completion) finished separate saved

end FormalSW.PyAst.HeapCalls.Framing
