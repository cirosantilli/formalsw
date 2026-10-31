import lang.py.FormalSW.IteratorTraversal

/-! Finite yielding prefixes need no assumption about later iterator behavior. -/
namespace FormalSW.PyAst.IteratorCalls
open HeapCalls HeapCalls.Relocation Mutable.Relocation
set_option Elab.async false

inductive YieldPrefix {α : Type} (module : Module) (choices : ChoiceSchedule)
    (iterator : Mutable.Value) (encode : α → Mutable.Value) :
    Mutable.Heap → Nat → List α → Mutable.Heap → Nat → Prop
  | nil {heap used} : YieldPrefix module choices iterator encode heap used [] heap used
  | cons {before middle after used nextUsed finalUsed value values}
      (ran : NextRun module choices iterator before used (.ok (encode value)) middle nextUsed)
      (rest : YieldPrefix module choices iterator encode middle nextUsed values after finalUsed) :
      YieldPrefix module choices iterator encode before used (value :: values) after finalUsed

theorem YieldPrefix.effects {α : Type} {module : Module} {choices : ChoiceSchedule} {iterator : Mutable.Value}
    {encode : α → Mutable.Value} {before after : Mutable.Heap} {used finalUsed : Nat} {values : List α}
    (trace : YieldPrefix module choices iterator encode before used values after finalUsed)
    (source : Relocation.ModuleSource module) (closed : Closed before) :
    Closed after ∧ before.length ≤ after.length := by
  induction trace with
  | nil => exact ⟨closed, Nat.le_refl _⟩
  | cons ran _ ih =>
      obtain ⟨middleClosed, grows⟩ := ran.effects source closed
      obtain ⟨afterClosed, later⟩ := ih middleClosed
      exact ⟨afterClosed, Nat.le_trans grows later⟩

theorem YieldPrefix.then_traversal {α : Type} {module : Module} {choices : ChoiceSchedule} {iterator : Mutable.Value}
    {encode : α → Mutable.Value} {before middle after : Mutable.Heap} {used nextUsed finalUsed : Nat}
    {values rest : List α} {outcome : Except ExceptionObject Unit}
    (first : YieldPrefix module choices iterator encode before used values middle nextUsed)
    (later : Traversal module choices iterator encode middle nextUsed rest outcome after finalUsed) :
    Traversal module choices iterator encode before used (values ++ rest) outcome after finalUsed := by
  induction first with
  | nil => exact later
  | cons ran _ ih => exact .yielded ran (ih later)

theorem Traversal.split {α : Type} {module : Module} {choices : ChoiceSchedule} {iterator : Mutable.Value}
    {encode : α → Mutable.Value} {before after : Mutable.Heap} {used finalUsed : Nat}
    (values rest : List α) {outcome : Except ExceptionObject Unit}
    (trace : Traversal module choices iterator encode before used (values ++ rest) outcome after finalUsed) :
    ∃ middle nextUsed, YieldPrefix module choices iterator encode before used values middle nextUsed ∧
      Traversal module choices iterator encode middle nextUsed rest outcome after finalUsed := by
  induction values generalizing before used with
  | nil => exact ⟨before, used, .nil, trace⟩
  | cons value values ih =>
      cases trace with
      | yielded ran later =>
          obtain ⟨middle, nextUsed, first, last⟩ := ih later
          exact ⟨middle, nextUsed, .cons ran first, last⟩

theorem Traversal.decompose {α : Type} {module : Module} {choices : ChoiceSchedule} {iterator : Mutable.Value}
    {encode : α → Mutable.Value} {before after : Mutable.Heap} {used finalUsed : Nat}
    {values : List α} {outcome : Except ExceptionObject Unit}
    (trace : Traversal module choices iterator encode before used values outcome after finalUsed) :
    ∃ middle nextUsed error, YieldPrefix module choices iterator encode before used values middle nextUsed ∧
      NextRun module choices iterator middle nextUsed (.error error) after finalUsed ∧ exitOutcome error = outcome := by
  induction trace with
  | exhausted ran => exact ⟨_, _, _, .nil, ran, rfl⟩
  | failed ran notExhausted => exact ⟨_, _, _, .nil, ran, by simp only [exitOutcome, if_neg notExhausted]⟩
  | yielded ran _ ih =>
      obtain ⟨middle, nextUsed, error, first, last, result⟩ := ih
      exact ⟨middle, nextUsed, error, .cons ran first, last, result⟩

/-- Ordinary validation does not consume set choices, even when it raises an exception. -/
theorem completion_of_heap {module : Module} {anchors used : Nat} {choices : ChoiceSchedule}
    {globals : Mutable.Globals} {core : HeapCalls.State} {outcome : Except ExceptionObject Mutable.Completion}
    (finished : Finishes (HeapCalls.step module anchors · globals) core outcome)
    (safe : ∀ completion, outcome = .ok completion → completion.outcome ≠ .error ⟨"TypeError", []⟩)
    (resumes : List Resume) :
    Reaches module anchors choices globals (.running ⟨core, used⟩ resumes) (.completed outcome used resumes) := by
  induction finished with
  | @done core outcome terminal =>
      have terminalSet : SetCalls.step module anchors choices ⟨core, used⟩ globals = .done outcome := by
        simp [SetCalls.step, terminal, SetCalls.liftStep]
      have ordinary : intercept module anchors ⟨core, used⟩ resumes globals = none := by
        apply Classical.byContradiction
        intro handled
        have collision := intercept_error (choices := choices) handled
        rw [terminalSet] at collision
        exact safe _ (Step.done.inj collision) rfl
      exact .next (core_done ordinary terminalSet) .refl
  | @next state following _ transition _ ih =>
      have transitionSet : SetCalls.step module anchors choices ⟨state, used⟩ globals = .next ⟨following, used⟩ := by
        simp [SetCalls.step, transition, SetCalls.liftStep]
      exact .next (core_next (intercept_none_of_next transitionSet) transitionSet) (ih safe)

theorem NextRun.scalar_isolated {module : Module} {choices : ChoiceSchedule} {iterator : Mutable.Value}
    {before after : Mutable.Heap} {used finalUsed : Nat} {value : Constant}
    (ran : NextRun module choices iterator before used (.ok (.scalar value)) after finalUsed)
    (source : Relocation.ModuleSource module) (physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout before physical rename) (noGrowth : after.length = before.length) (anchors : Nat) :
    ∃ other, ExecutionLayout after other rename ∧
      (∀ address object, PrivateLayout before physical rename address object →
        PrivateLayout after other rename address object) ∧
      ∀ loop resumes, Reaches module anchors choices []
        (.running ⟨⟨.block (loopCode loop (relocateValue rename iterator) :: loop.following) loop.env,
          loop.stack, physical⟩, used⟩ resumes)
        (.running ⟨⟨.block (loop.body ++ [Calls.loopContinuation loop.body (loopCode loop (relocateValue rename iterator))]
          ++ loop.following) (setLocal loop.env loop.name (.scalar value)),
          loop.stack, other⟩, finalUsed⟩ resumes) := by
  obtain ⟨operation, inside, isObject, bound, executed⟩ := ran
  obtain ⟨other, nextMap, extended, kept, called⟩ := Relocation.advance_completion_isolated
    module choices before physical rename before.length anchors used finalUsed iterator operation
    (.ok (.scalar value)) after [] source layout inside (by simp [GlobalsWithin]) isObject bound executed noGrowth
  have same : ∀ index < after.length, rename index = nextMap index := by
    intro index bounded
    exact (extended.agrees index (by omega)).symm
  refine ⟨other, extended.layout.congr same, fun address object initial =>
    (kept address object initial).congr same, ?_⟩
  intro loop resumes
  apply advanced
  simpa only [relocateGlobals, List.map_nil, Except.map, relocateValue] using called loop resumes

end FormalSW.PyAst.IteratorCalls
