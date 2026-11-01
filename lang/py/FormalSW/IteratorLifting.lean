import lang.py.FormalSW.IteratorCalls

/-! Reuse ordinary source execution inside iterator protocol calls and loop bodies. -/
namespace FormalSW.PyAst.IteratorCalls
open HeapCalls
set_option Elab.async false

theorem intercept_error {module : Module} {anchors : Nat} {choices : ChoiceSchedule}
    {globals : Mutable.Globals} {core : SetCalls.State} {resumes : List Resume}
    (handled : intercept module anchors core resumes globals ≠ none) :
    SetCalls.step module anchors choices core globals = .done (.ok
      ⟨.error ⟨"TypeError", []⟩, globals, core.core.heap, anchors⟩) := by
  rcases core with ⟨⟨work, stack, heap⟩, used⟩
  cases work with
  | value value =>
      cases stack with
      | nil => simp [intercept] at handled
      | cons frame stack =>
          cases frame <;> simp only [intercept, ne_eq, not_true_eq_false] at handled
          rename_i name body otherwise following env
          have hasInstance : isInstance heap value = true := by
            cases found : isInstance heap value <;> simp_all
          simp [SetCalls.step, SetCalls.liftStep, HeapCalls.step, run, sequence_instance hasInstance,
            done, protectGenerator, Calls.generatorException]
  | block body env =>
      cases body with
      | nil => simp [intercept] at handled
      | cons statement body =>
          cases statement <;> simp only [intercept, ne_eq, not_true_eq_false] at handled
          rename_i name source position loop otherwise
          have hasInstance : isInstance heap (sequenceValue source) = true := by
            cases found : isInstance heap (sequenceValue source) <;> simp_all
          simp [SetCalls.step, SetCalls.liftStep, HeapCalls.step, run, sequence_instance hasInstance,
            done, protectGenerator, Calls.generatorException]
  | _ => simp [intercept] at handled

/-- Every ordinary nonterminal source step remains valid in the iterator interpreter. -/
theorem intercept_none_of_next {module : Module} {anchors : Nat} {choices : ChoiceSchedule}
    {globals : Mutable.Globals} {core following : SetCalls.State} {resumes : List Resume}
    (transition : SetCalls.step module anchors choices core globals = .next following) :
    intercept module anchors core resumes globals = none := by
  apply Classical.byContradiction
  intro handled
  have terminal := intercept_error (choices := choices) handled
  rw [transition] at terminal
  cases terminal

theorem Reaches.of_set {module : Module} {anchors : Nat} {choices : ChoiceSchedule}
    {globals : Mutable.Globals} {first final : SetCalls.State}
    (before : SetCalls.Reaches choices module anchors first final (globals := globals))
    (resumes : List Resume) :
    Reaches module anchors choices globals (.running first resumes) (.running final resumes) := by
  induction before with
  | refl => exact .refl
  | next transition _ ih =>
      exact .next (core_next (intercept_none_of_next transition) transition) ih

/-- Successful results and non-TypeError failures lift from the sequence interpreter.
Its TypeError for instance iteration is intentionally replaced by the protocol. -/
theorem completion_of_set {module : Module} {anchors : Nat} {choices : ChoiceSchedule}
    {globals : Mutable.Globals} {core : SetCalls.State}
    {outcome : Except ExceptionObject Mutable.Completion}
    (finished : Finishes (SetCalls.step module anchors choices · globals) core outcome)
    (safe : ∀ completion, outcome = .ok completion →
      completion.outcome ≠ .error ⟨"TypeError", []⟩)
    (resumes : List Resume) :
    ∃ used, Reaches module anchors choices globals (.running core resumes)
      (.completed outcome used resumes) := by
  induction finished with
  | @done core outcome terminal =>
      have ordinary : intercept module anchors core resumes globals = none := by
        apply Classical.byContradiction
        intro handled
        have collision := intercept_error (choices := choices) handled
        rw [terminal] at collision
        exact safe _ (Step.done.inj collision) rfl
      exact ⟨core.choicesUsed, .next (core_done ordinary terminal) .refl⟩
  | next transition _ ih =>
      obtain ⟨used, after⟩ := ih safe
      exact ⟨used, .next (core_next (intercept_none_of_next transition) transition) after⟩

theorem finishes_of_set {module : Module} {anchors : Nat} {choices : ChoiceSchedule}
    {globals : Mutable.Globals} {core : SetCalls.State}
    {outcome : Except ExceptionObject Mutable.Completion}
    (finished : Finishes (SetCalls.step module anchors choices · globals) core outcome)
    (safe : ∀ completion, outcome = .ok completion →
      completion.outcome ≠ .error ⟨"TypeError", []⟩) :
    Finishes (step module anchors choices · globals) (.running core []) outcome := by
  obtain ⟨used, before⟩ := completion_of_set finished safe []
  exact before.finishes (.done rfl)

end FormalSW.PyAst.IteratorCalls
