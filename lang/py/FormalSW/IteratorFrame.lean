import lang.py.FormalSW.ProtocolHeapFrame
import lang.py.FormalSW.SetFrame
import lang.py.FormalSW.IteratorCalls

/-! Private cells survive protocol binding, method execution and resumption of suspended consumers. -/
namespace FormalSW.PyAst.IteratorCalls.Framing
open Mutable Mutable.Relocation
set_option Elab.async false

def StateCell (address : Nat) (object : Object) : State → Prop
  | .running core _ => SavedCell address object core.core.heap
  | .completed (.ok completion) _ _ => SavedCell address object completion.heap
  | .completed (.error _) _ _ => True

def RetainsCell (address : Nat) (object : Object) : Step State Completion → Prop
  | .next state => StateCell address object state
  | .done (.ok completion) => SavedCell address object completion.heap
  | .done (.error _) | .unsupported => True

def StateSeparate (address : Nat) : State → Prop
  | .running core _ => HeapCalls.Framing.StateSeparate address core.core
  | .completed _ _ _ => True

theorem lift_retains_cell (address used : Nat) (object : Object) (resumes : List Resume)
    (transition : Step SetCalls.State Completion)
    (retained : SetCalls.Framing.RetainsCell address object transition) :
    RetainsCell address object (lift used resumes transition) := by
  cases transition with
  | next | unsupported => exact retained
  | done outcome => cases outcome <;> exact retained

theorem propagate_retains_cell (address used : Nat) (object : Object) (loop : Loop)
    (completion : Completion) (resumes : List Resume) (saved : SavedCell address object completion.heap) :
    RetainsCell address object (propagate loop completion used resumes) := saved

theorem resume_retains_cell (module : Module) (address used : Nat) (object : Object)
    (completion : Completion) (pending : Resume) (rest : List Resume)
    (saved : SavedCell address object completion.heap) :
    RetainsCell address object (resume module completion used pending rest) := by
  cases pending with
  | acquire loop =>
    cases checked : ProtocolCalls.iterFinish module completion with
    | none => simp only [resume, checked, RetainsCell]
    | some result =>
      have retained := Heapq.iterFinish_preserves (SavedCell address object) module completion result saved checked
      cases outcome : result.outcome <;> simp only [resume, checked, outcome]
      · exact propagate_retains_cell address used object loop result rest retained
      · exact retained
  | advance loop iterator =>
    cases outcome : completion.outcome with
    | ok value => simpa only [resume, outcome, RetainsCell, StateCell] using saved
    | error error =>
      simp only [resume, outcome]
      split
      · exact saved
      · exact propagate_retains_cell address used object loop completion rest saved

theorem enter_retains_cell (address anchors used : Nat) (object : Object) (heap : Heap)
    (resumes : List Resume) (pending : Resume) (method : Eval HeapCalls.Operation) (globals : Globals)
    (saved : SavedCell address object heap) (preserved : Heapq.Preserves (SavedCell address object) method) :
    RetainsCell address object (enter anchors heap used resumes pending method globals) := by
  cases executed : method heap with
  | none => simp only [enter, executed, RetainsCell]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have retained := preserved heap outcome after saved executed
    cases outcome <;> simpa only [enter, executed, RetainsCell, StateCell] using retained

theorem intercept_retains_cell (module : Module) (address anchors : Nat) (object : Object)
    (core : SetCalls.State) (resumes : List Resume) (globals : Globals)
    (transition : Step State Completion) (saved : SavedCell address object core.core.heap)
    (intercepted : intercept module anchors core resumes globals = some transition) :
    RetainsCell address object transition := by
  rcases core with ⟨⟨work, stack, heap⟩, used⟩
  simp only [intercept] at intercepted
  split at intercepted
  · split at intercepted
    · cases intercepted
      exact enter_retains_cell address anchors used object heap resumes _ _ globals saved
        (Heapq.preserves_iterMethod _ module _)
    · cases intercepted
  · split at intercepted
    · cases intercepted
      apply enter_retains_cell address anchors used object heap resumes _ _ globals saved
      with_reducible apply Heapq.Preserves.bind _ _ _ (Heapq.preserves_nextMethod _ module _)
      intro operation
      cases operation
      · exact Heapq.Preserves.error _ "TypeError"
      · exact Heapq.Preserves.pure _ _
    · cases intercepted
  · cases intercepted

theorem step_cell (module : Module) (address anchors : Nat) (object : Object) (state : State)
    (choices : ChoiceSchedule) (globals : Globals) (separate : StateSeparate address state)
    (saved : StateCell address object state) :
    RetainsCell address object (step module anchors choices state globals) := by
  cases state with
  | running core resumes =>
    cases intercepted : intercept module anchors core resumes globals with
    | some transition =>
      simpa only [step, intercepted] using
        intercept_retains_cell module address anchors object core resumes globals transition saved intercepted
    | none =>
      simp only [step, intercepted]
      exact lift_retains_cell address core.choicesUsed object resumes _
        (SetCalls.Framing.step_cell module address anchors object core choices globals separate saved)
  | completed outcome used resumes =>
    cases resumes with
    | nil => cases outcome <;> exact saved
    | cons pending rest =>
      cases outcome with
      | error error => trivial
      | ok completion => exact resume_retains_cell module address used object completion pending rest saved

/-- Separation is checked only on this finite prefix; its final consumer may write later. -/
inductive SeparatedReaches (module : Module) (anchors address : Nat) (choices : ChoiceSchedule)
    (globals : Globals) : State → State → Prop where
  | refl {state : State} : SeparatedReaches module anchors address choices globals state state
  | next {state following final : State} : StateSeparate address state → step module anchors choices state globals = .next following →
      SeparatedReaches module anchors address choices globals following final →
      SeparatedReaches module anchors address choices globals state final

theorem SeparatedReaches.reaches {module : Module} {anchors address : Nat} {choices : ChoiceSchedule}
    {globals : Globals} {initial final : State}
    (path : SeparatedReaches module anchors address choices globals initial final) :
    Reaches module anchors choices globals initial final := by
  induction path with
  | refl => exact .refl
  | next _ transition _ ih => exact .next transition ih

theorem SeparatedReaches.retains_cell {module : Module} {anchors address : Nat} {choices : ChoiceSchedule}
    {globals : Globals} {initial final : State} (object : Object)
    (path : SeparatedReaches module anchors address choices globals initial final)
    (saved : StateCell address object initial) : StateCell address object final := by
  induction path with
  | refl => exact saved
  | @next state following final separate transition path ih =>
    have retained := step_cell module address anchors object state choices globals separate saved
    exact ih (by simpa only [transition, RetainsCell] using retained)

/-- Every write reached inside a protocol method must be separate from the protected cell. -/
theorem reaches_cell (module : Module) (address anchors : Nat) (object : Object)
    (choices : ChoiceSchedule) (globals : Globals) (initial final : State)
    (path : Reaches module anchors choices globals initial final)
    (separate : ∀ state, Reaches module anchors choices globals initial state → StateSeparate address state)
    (saved : StateCell address object initial) : StateCell address object final := by
  induction path with
  | refl => exact saved
  | @next state following final transition path ih =>
    apply ih
    · intro state reached
      exact separate state (.next transition reached)
    · have retained := step_cell module address anchors object state choices globals (separate state .refl) saved
      simpa only [transition, RetainsCell] using retained

theorem finishes_retains_cell (module : Module) (address anchors : Nat) (object : Object)
    (choices : ChoiceSchedule) (globals : Globals) (initial : State) (outcome : Except ExceptionObject Completion)
    (finished : Finishes (step module anchors choices · globals) initial outcome)
    (separate : ∀ state, Reaches module anchors choices globals initial state → StateSeparate address state)
    (saved : StateCell address object initial) : RetainsCell address object (.done outcome) := by
  induction finished with
  | @done state outcome transition =>
    have retained := step_cell module address anchors object state choices globals (separate state .refl) saved
    simpa only [transition] using retained
  | @next state following outcome transition rest ih =>
    apply ih
    · intro state reached
      exact separate state (.next transition reached)
    · have retained := step_cell module address anchors object state choices globals (separate state .refl) saved
      simpa only [transition, RetainsCell] using retained

theorem finishes_cell (module : Module) (address anchors : Nat) (object : Object)
    (choices : ChoiceSchedule) (globals : Globals) (initial : State) (completion : Completion)
    (finished : Finishes (step module anchors choices · globals) initial (.ok completion))
    (separate : ∀ state, Reaches module anchors choices globals initial state → StateSeparate address state)
    (saved : StateCell address object initial) : SavedCell address object completion.heap :=
  finishes_retains_cell module address anchors object choices globals initial (.ok completion) finished separate saved

end FormalSW.PyAst.IteratorCalls.Framing
