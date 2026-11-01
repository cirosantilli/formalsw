import lang.py.FormalSW.SetCalls

/-! Supported set executions retain their source meaning when imported into a larger module. -/
namespace FormalSW.PyAst.SetCalls
open HeapCalls
set_option Elab.async false

variable {source target : Module} {anchors : Nat} {choices : ChoiceSchedule}
  {globals : Mutable.Globals}

/-- The set fallback only handles primitive work, whose ordinary step does not inspect the module. -/
theorem iteratorStep_module_independent (state : State)
    (supported : iteratorStep choices anchors state globals ≠ .unsupported) :
    HeapCalls.step target anchors state.core globals = HeapCalls.step source anchors state.core globals := by
  rcases state with ⟨⟨work, stack, heap⟩, used⟩
  cases work with
  | operation operation values =>
      cases operation <;> first | rfl | simp [iteratorStep] at supported
  | value value =>
      cases stack with
      | nil => rfl
      | cons frame stack =>
          cases frame <;> first | rfl | simp [iteratorStep] at supported
  | dictionary remaining _ _ => cases remaining <;> rfl
  | _ => rfl

theorem step_extend (extension : Extends target source) (state : State)
    (supported : step source anchors choices state globals ≠ .unsupported) :
    step target anchors choices state globals = step source anchors choices state globals := by
  by_cases ordinary : HeapCalls.step source anchors state.core globals = .unsupported
  · have fallback : iteratorStep choices anchors state globals ≠ .unsupported := by
      simpa only [step, ordinary] using supported
    simp only [step, iteratorStep_module_independent (source := source) (target := target) state fallback, ordinary]
  · simp only [step, HeapCalls.step_extend extension state.core ordinary]

theorem Reaches.extend {first final : State}
    (ran : Reaches choices source anchors first final globals) (extension : Extends target source) :
    Reaches choices target anchors first final globals := by
  induction ran with
  | refl => exact .refl
  | next transition _ ih =>
      exact .next (by rw [step_extend extension _ (by simp [transition])]; exact transition) ih

theorem finishes_extend {state : State} {outcome : Except ExceptionObject Mutable.Completion}
    (ran : Finishes (step source anchors choices · globals) state outcome)
    (extension : Extends target source) :
    Finishes (step target anchors choices · globals) state outcome := by
  induction ran with
  | done terminal =>
      exact .done (by rw [step_extend extension _ (by simp [terminal])]; exact terminal)
  | next transition _ ih =>
      exact .next (by rw [step_extend extension _ (by simp [transition])]; exact transition) ih

end FormalSW.PyAst.SetCalls
