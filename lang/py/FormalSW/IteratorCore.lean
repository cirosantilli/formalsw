import lang.py.FormalSW.IteratorEntry

/-! Ordinary steps retain suspended custom loops as allocation extends their address map. -/
namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation
set_option Elab.async false

theorem relocateResumes_congr (left right : Nat → Nat) (limit : Nat) (resumes : List Resume)
    (agree : ∀ address < limit, left address = right address)
    (inside : ∀ pending ∈ resumes, ResumeWithin limit pending) :
    resumes.map (relocateResume left) = resumes.map (relocateResume right) :=
  List.map_congr_left (fun pending member => relocateResume_congr left right limit pending agree (inside pending member))

/-- The two core steps may allocate at different addresses. Only old references must agree. -/
theorem step_ordinary_relocates (module : Module) (core : SetCalls.State)
    (physical physicalAfter : Mutable.Heap) (rename nextMap : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (choices : ChoiceSchedule) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module)
    (layout : RuntimeLayout core.core.heap physical rename)
    (workInside : WorkWithin core.core.heap.length core.core.work)
    (saved : ∀ pending ∈ resumes, ResumeWithin core.core.heap.length pending)
    (agree : ∀ address < core.core.heap.length, nextMap address = rename address)
    (ordinary : intercept module logicalAnchors core resumes globals = none)
    (paired : SetCalls.step module physicalAnchors choices (relocateCore rename physical core)
        (relocateGlobals rename globals) =
      (SetCalls.step module logicalAnchors choices core globals).map
        (relocateCore nextMap physicalAfter) (relocateCompletion nextMap physicalAfter physicalAnchors)) :
    IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.running core resumes)) (relocateGlobals rename globals) =
      relocateStep nextMap physicalAfter physicalAnchors
        (IteratorCalls.step module logicalAnchors choices (.running core resumes) globals) := by
  have dispatch := intercept_relocates module core physical rename logicalAnchors physicalAnchors resumes globals source layout workInside
  have same := relocateResumes_congr nextMap rename core.core.heap.length resumes agree saved
  simp only [relocateState, IteratorCalls.step, dispatch, ordinary, Option.map_none, paired]
  change lift core.choicesUsed (resumes.map (relocateResume rename))
    ((SetCalls.step module logicalAnchors choices core globals).map
      (relocateCore nextMap physicalAfter) (relocateCompletion nextMap physicalAfter physicalAnchors)) = _
  rw [← same]
  exact lift_relocates nextMap physicalAfter physicalAnchors core.choicesUsed resumes _

/-- The set wrapper leaves every supported heap step unchanged. -/
theorem set_step_supported (module : Module) (core : HeapCalls.State) (anchors used : Nat)
    (choices : ChoiceSchedule) (globals : Mutable.Globals) (transition : Step HeapCalls.State Mutable.Completion)
    (executed : HeapCalls.step module anchors core globals = transition) (supported : transition ≠ .unsupported) :
    SetCalls.step module anchors choices ⟨core, used⟩ globals = SetCalls.liftStep used transition := by
  simp only [SetCalls.step, executed]

theorem set_lift_relocates (rename : Nat → Nat) (physical : Mutable.Heap) (anchors used : Nat)
    (transition : Step HeapCalls.State Mutable.Completion) :
    SetCalls.liftStep used (HeapCalls.Relocation.relocateStep rename physical anchors transition) =
      (SetCalls.liftStep used transition).map
        (relocateCore rename physical) (relocateCompletion rename physical anchors) := by
  cases transition <;> rfl

/-- Reuse a proved ordinary heap step, retaining the separate set-choice position. -/
theorem set_step_relocates (module : Module) (core : HeapCalls.State)
    (physical physicalAfter : Mutable.Heap) (rename nextMap : Nat → Nat)
    (logicalAnchors physicalAnchors used : Nat) (choices : ChoiceSchedule) (globals : Mutable.Globals)
    (supported : HeapCalls.step module logicalAnchors core globals ≠ .unsupported)
    (paired : HeapCalls.step module physicalAnchors (HeapCalls.Relocation.relocateState rename physical core)
        (relocateGlobals rename globals) =
      HeapCalls.Relocation.relocateStep nextMap physicalAfter physicalAnchors
        (HeapCalls.step module logicalAnchors core globals)) :
    SetCalls.step module physicalAnchors choices (relocateCore rename physical ⟨core, used⟩)
        (relocateGlobals rename globals) =
      (SetCalls.step module logicalAnchors choices ⟨core, used⟩ globals).map
        (relocateCore nextMap physicalAfter) (relocateCompletion nextMap physicalAfter physicalAnchors) := by
  have movedSupported : HeapCalls.Relocation.relocateStep nextMap physicalAfter physicalAnchors
      (HeapCalls.step module logicalAnchors core globals) ≠ .unsupported := by
    cases tested : HeapCalls.step module logicalAnchors core globals <;> simp_all [HeapCalls.Relocation.relocateStep]
  rw [set_step_supported module core logicalAnchors used choices globals _ rfl supported]
  change SetCalls.step module physicalAnchors choices
    ⟨HeapCalls.Relocation.relocateState rename physical core, used⟩ (relocateGlobals rename globals) = _
  rw [set_step_supported module _ physicalAnchors used choices _ _ paired movedSupported]
  exact set_lift_relocates nextMap physicalAfter physicalAnchors used _

/-- Transfer the core's bounds after growth to all suspended consumers. -/
theorem running_within_after {before : Nat} {core : SetCalls.State} {resumes : List Resume}
    (larger : before ≤ core.core.heap.length) (inside : HeapCalls.Relocation.StateWithin core.core)
    (saved : ∀ pending ∈ resumes, ResumeWithin before pending) :
    StateWithin core.core.heap.length (.running core resumes) :=
  ⟨inside.1, inside.2, fun pending member => ResumeWithin.mono (saved pending member) larger⟩

/-- A method's completed heap can grow even when the next transition delivers an exception. -/
theorem completed_within_after {before : Nat} {completion : Mutable.Completion}
    (used : Nat) (resumes : List Resume) (larger : before ≤ completion.heap.length)
    (inside : CompletionWithin completion) (saved : ∀ pending ∈ resumes, ResumeWithin before pending) :
    StateWithin completion.heap.length (.completed (.ok completion) used resumes) :=
  ⟨inside.1, inside.2, fun pending member => ResumeWithin.mono (saved pending member) larger⟩

end FormalSW.PyAst.IteratorCalls.Relocation
