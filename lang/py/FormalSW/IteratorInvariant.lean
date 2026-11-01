import lang.py.FormalSW.SetIteratorInvariant

/-! Iterator dispatch and saved consumers preserve the core execution invariant. -/
namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation
set_option Elab.async false

/-- Unsupported protocol errors carry no runtime heap. -/
def StateHeap (heap : Mutable.Heap) : State → Prop
  | .running core _ => core.core.heap = heap
  | .completed (.ok completion) _ _ => completion.heap = heap
  | .completed (.error _) _ _ => True

def StepHeap (heap : Mutable.Heap) : Step State Mutable.Completion → Prop
  | .next state => StateHeap heap state
  | .done (.ok completion) => completion.heap = heap
  | .done (.error _) | .unsupported => True

/-- The next step retains the caller layout, saved references, and old address mappings. -/
def Preserves (logical physical : Mutable.Heap) (rename : Nat → Nat) (anchors : Nat)
    (left right : Step State Mutable.Completion) : Prop :=
  ∃ logicalAfter physicalAfter nextMap,
    (∀ address < logical.length, nextMap address = rename address) ∧
    logical.length ≤ logicalAfter.length ∧ physical.length ≤ physicalAfter.length ∧
    ExecutionLayout logicalAfter physicalAfter nextMap ∧
    StepHeap logicalAfter left ∧ StepWithin logicalAfter.length left ∧
    right = relocateStep nextMap physicalAfter anchors left

theorem Preserves.unchanged {logical physical : Mutable.Heap} {rename : Nat → Nat} {anchors : Nat}
    {left right : Step State Mutable.Completion} (layout : ExecutionLayout logical physical rename)
    (heap : StepHeap logical left) (inside : StepWithin logical.length left)
    (paired : right = relocateStep rename physical anchors left) : Preserves logical physical rename anchors left right :=
  ⟨logical, physical, rename, fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _, layout, heap, inside, paired⟩

theorem lift_invariant (before : Nat) (heap : Mutable.Heap) (used : Nat) (resumes : List Resume)
    (transition : Step SetCalls.State Mutable.Completion) (grows : before ≤ heap.length)
    (saved : ∀ pending ∈ resumes, ResumeWithin before pending)
    (retained : SetCalls.Relocation.StepHeap heap transition)
    (inside : SetCalls.Relocation.StepWithin transition) :
    StepHeap heap (lift used resumes transition) ∧ StepWithin heap.length (lift used resumes transition) := by
  cases transition with
  | next core =>
    have same : core.core.heap = heap := retained
    subst heap
    exact ⟨rfl, running_within_after grows inside saved⟩
  | done outcome =>
    cases outcome with
    | ok completion =>
      have same : completion.heap = heap := retained
      subst heap
      exact ⟨rfl, completed_within_after used resumes grows inside saved⟩
    | error exception => exact ⟨trivial, fun pending member => (saved pending member).mono grows⟩
  | unsupported => exact ⟨trivial, trivial⟩

/-- A core allocation also updates the map used by every suspended consumer. -/
theorem lift_preserves {logical physical : Mutable.Heap} {rename : Nat → Nat} {anchors : Nat}
    {left right : Step SetCalls.State Mutable.Completion}
    (preserved : SetCalls.Relocation.Preserves logical physical rename anchors left right)
    (used : Nat) (resumes : List Resume) (saved : ∀ pending ∈ resumes, ResumeWithin logical.length pending) :
    Preserves logical physical rename anchors (lift used resumes left)
      (lift used (resumes.map (relocateResume rename)) right) := by
  obtain ⟨logicalAfter, physicalAfter, nextMap, agree, grows, physicalGrows, layout, heap, inside, paired⟩ := preserved
  have invariant := lift_invariant logical.length logicalAfter used resumes left grows saved heap inside
  refine ⟨logicalAfter, physicalAfter, nextMap, agree, grows, physicalGrows, layout, invariant.1, invariant.2, ?_⟩
  rw [paired, ← relocateResumes_congr nextMap rename logical.length resumes agree saved]
  exact lift_relocates nextMap physicalAfter anchors used resumes left

theorem step_ordinary_preserves (module : Module) (core : SetCalls.State)
    (physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (choices : ChoiceSchedule) (resumes : List Resume) (globals : Mutable.Globals)
    (source : ModuleSource module) (layout : ExecutionLayout core.core.heap physical rename)
    (inside : StateWithin core.core.heap.length (.running core resumes))
    (ordinary : intercept module logicalAnchors core resumes globals = none)
    (preserved : SetCalls.Relocation.Preserves core.core.heap physical rename physicalAnchors
      (SetCalls.step module logicalAnchors choices core globals)
      (SetCalls.step module physicalAnchors choices (relocateCore rename physical core) (relocateGlobals rename globals))) :
    Preserves core.core.heap physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices (.running core resumes) globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.running core resumes)) (relocateGlobals rename globals)) := by
  have dispatch := intercept_relocates module core physical rename logicalAnchors physicalAnchors resumes globals source layout.runtime inside.1
  simpa only [IteratorCalls.step, relocateState, dispatch, ordinary, Option.map_none] using
    lift_preserves preserved core.choicesUsed resumes inside.2.2

theorem propagate_heap (loop : Loop) (completion : Mutable.Completion) (used : Nat) (resumes : List Resume) :
    StepHeap completion.heap (propagate loop completion used resumes) := rfl

theorem resume_heap (module : Module) (completion : Mutable.Completion) (used : Nat)
    (pending : Resume) (rest : List Resume)
    (inside : ∀ value, completion.outcome = .ok value → value.edge.Within completion.heap.length) :
    StepHeap completion.heap (resume module completion used pending rest) := by
  cases pending with
  | acquire loop =>
    cases tested : ProtocolCalls.iterFinish module completion with
    | none => simp [resume, tested, StepHeap]
    | some checked =>
      have unchanged := (iterFinish_effect module completion checked inside tested).1
      cases outcome : checked.outcome <;>
        simpa only [resume, tested, outcome, StepHeap, StateHeap, propagate] using unchanged
  | advance loop iterator =>
    cases outcome : completion.outcome with
    | ok value => simp [resume, outcome, StepHeap, StateHeap]
    | error exception =>
      simp only [resume, outcome]
      split <;> rfl

theorem step_completed_preserves (module : Module) (choices : ChoiceSchedule)
    (completion : Mutable.Completion) (physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors used : Nat) (resumes : List Resume) (globals : Mutable.Globals)
    (layout : ExecutionLayout completion.heap physical rename) (inside : CompletionWithin completion)
    (saved : ∀ pending ∈ resumes, ResumeWithin completion.heap.length pending) :
    Preserves completion.heap physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices (.completed (.ok completion) used resumes) globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.completed (.ok completion) used resumes)) (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · cases resumes with
    | nil => rfl
    | cons pending rest => exact resume_heap module completion used pending rest inside.2
  · exact step_completed_within module choices completion logicalAnchors used resumes inside saved
  · exact step_completed_relocates module choices completion physical rename logicalAnchors physicalAnchors used resumes layout.runtime inside.2

theorem step_completed_error_preserves (module : Module) (choices : ChoiceSchedule)
    (exception : ExceptionObject) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors used : Nat) (resumes : List Resume) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (saved : ∀ pending ∈ resumes, ResumeWithin logical.length pending) :
    Preserves logical physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices (.completed (.error exception) used resumes) globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.completed (.error exception) used resumes)) (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · cases resumes <;> trivial
  · exact step_completed_error_within module choices exception logical.length logicalAnchors used resumes saved
  · exact step_completed_error_relocates module choices exception physical rename logicalAnchors physicalAnchors used resumes

theorem iterMethod_keeps_heap (module : Module) (heap after : Mutable.Heap) (value : Mutable.Value)
    (outcome : Except ExceptionObject Operation) (inside : value.edge.Within heap.length)
    (executed : ProtocolCalls.iterMethod module value heap = some (outcome, after)) : after = heap := by
  have same := iterMethod_relocates (RuntimeLayout.refl heap) module value inside
  simp only [relocateValue_id, executed, Option.map_some] at same
  exact congrArg Prod.snd (Option.some.inj same)

theorem advanceMethod_keeps_heap (module : Module) (heap after : Mutable.Heap) (value : Mutable.Value)
    (outcome : Except ExceptionObject Operation) (source : ModuleSource module) (inside : value.edge.Within heap.length)
    (executed : advanceMethod module value heap = some (outcome, after)) : after = heap := by
  have same := advanceMethod_relocates (RuntimeLayout.refl heap) module value source inside
  simp only [relocateValue_id, executed, Option.map_some] at same
  exact congrArg Prod.snd (Option.some.inj same)

theorem enter_heap (anchors used : Nat) (heap : Mutable.Heap) (resumes : List Resume)
    (pending : Resume) (method : Mutable.Eval Operation) (globals : Mutable.Globals)
    (unchanged : ∀ outcome after, method heap = some (outcome, after) → after = heap) :
    StepHeap heap (enter anchors heap used resumes pending method globals) := by
  cases tested : method heap with
  | none => simp [enter, tested, StepHeap]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have same := unchanged outcome after tested
    subst after
    cases outcome <;> simp [enter, tested, StepHeap, StateHeap]

theorem intercept_heap (module : Module) (core : SetCalls.State) (anchors : Nat)
    (resumes : List Resume) (globals : Mutable.Globals) (transition : Step State Mutable.Completion)
    (source : ModuleSource module) (inside : WorkWithin core.core.heap.length core.core.work)
    (intercepted : intercept module anchors core resumes globals = some transition) :
    StepHeap core.core.heap transition := by
  rcases core with ⟨⟨work, stack, heap⟩, used⟩
  cases work with
  | value receiver =>
    cases stack with
    | nil => simp [intercept] at intercepted
    | cons frame stack =>
      cases frame with
      | sequence name body otherwise following env =>
        simp only [intercept] at intercepted
        split at intercepted
        · cases intercepted
          exact enter_heap anchors used heap resumes _ _ globals
            (fun outcome after found => iterMethod_keeps_heap module heap after receiver outcome inside found)
        · cases intercepted
      | _ => simp [intercept] at intercepted
  | block statements env =>
    cases statements with
    | nil => simp [intercept] at intercepted
    | cons statement following =>
      cases statement with
      | sequenceStepLoop name cursor index body otherwise =>
        have bounded := inside.2 _ (List.mem_cons_self ..)
        simp only [StmtWithin] at bounded
        simp only [intercept] at intercepted
        split at intercepted
        · cases intercepted
          exact enter_heap anchors used heap resumes _ (advanceMethod module (sequenceValue cursor)) globals
            (fun outcome after found => advanceMethod_keeps_heap module heap after (sequenceValue cursor) outcome source bounded.1.value found)
        · cases intercepted
      | _ => simp [intercept] at intercepted
  | _ => simp [intercept] at intercepted

theorem step_intercepted_preserves (module : Module) (core : SetCalls.State)
    (physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (choices : ChoiceSchedule) (resumes : List Resume) (globals : Mutable.Globals)
    (transition : Step State Mutable.Completion) (source : ModuleSource module)
    (layout : ExecutionLayout core.core.heap physical rename)
    (inside : StateWithin core.core.heap.length (.running core resumes))
    (globalsInside : GlobalsWithin core.core.heap.length globals)
    (intercepted : intercept module logicalAnchors core resumes globals = some transition) :
    Preserves core.core.heap physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices (.running core resumes) globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.running core resumes)) (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · simpa only [IteratorCalls.step, intercepted] using
      intercept_heap module core logicalAnchors resumes globals transition source inside.1 intercepted
  · simpa only [IteratorCalls.step, intercepted] using
      intercept_within module core logicalAnchors resumes globals transition source inside globalsInside intercepted
  · exact step_intercepted_relocates module core physical rename logicalAnchors physicalAnchors choices resumes globals transition
      source layout.runtime inside.1 intercepted

/-- Every wrapper transition preserves the invariant once its ordinary core step does. -/
theorem step_preserves (module : Module) (choices : ChoiceSchedule) (state : State)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (heap : StateHeap logical state) (inside : StateWithin logical.length state)
    (globalsInside : GlobalsWithin logical.length globals)
    (corePreserves : ∀ core resumes, state = .running core resumes →
      intercept module logicalAnchors core resumes globals = none →
      SetCalls.Relocation.Preserves logical physical rename physicalAnchors
        (SetCalls.step module logicalAnchors choices core globals)
        (SetCalls.step module physicalAnchors choices (relocateCore rename physical core) (relocateGlobals rename globals))) :
    Preserves logical physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices state globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors state) (relocateGlobals rename globals)) := by
  cases state with
  | running core resumes =>
    have same : core.core.heap = logical := heap
    subst logical
    cases dispatched : intercept module logicalAnchors core resumes globals with
    | none =>
      exact step_ordinary_preserves module core physical rename logicalAnchors physicalAnchors choices resumes globals
        source layout inside dispatched (corePreserves core resumes rfl dispatched)
    | some transition =>
      exact step_intercepted_preserves module core physical rename logicalAnchors physicalAnchors choices resumes globals
        transition source layout inside globalsInside dispatched
  | completed outcome used resumes =>
    cases outcome with
    | error exception =>
      exact step_completed_error_preserves module choices exception logical physical rename
        logicalAnchors physicalAnchors used resumes globals layout inside
    | ok completion =>
      have same : completion.heap = logical := heap
      subst logical
      exact step_completed_preserves module choices completion physical rename logicalAnchors physicalAnchors used resumes globals
        layout ⟨inside.1, inside.2.1⟩ inside.2.2


/-- Expose the next wrapper state, including the roots retained across allocation. -/
theorem Preserves.next {logical physical : Mutable.Heap} {rename : Nat → Nat} {anchors : Nat}
    {next : State} {right : Step State Mutable.Completion}
    (preserved : Preserves logical physical rename anchors (.next next) right)
    (globals : Mutable.Globals) (globalsInside : GlobalsWithin logical.length globals) :
    ∃ logicalAfter physicalAfter nextMap,
      (∀ address < logical.length, nextMap address = rename address) ∧
      logical.length ≤ logicalAfter.length ∧ physical.length ≤ physicalAfter.length ∧
      ExecutionLayout logicalAfter physicalAfter nextMap ∧ StateHeap logicalAfter next ∧
      StateWithin logicalAfter.length next ∧ GlobalsWithin logicalAfter.length globals ∧
      relocateGlobals nextMap globals = relocateGlobals rename globals ∧
      right = .next (relocateState nextMap physicalAfter anchors next) := by
  obtain ⟨logicalAfter, physicalAfter, nextMap, agree, grows, physicalGrows, layout, heap, inside, paired⟩ := preserved
  exact ⟨logicalAfter, physicalAfter, nextMap, agree, grows, physicalGrows, layout, heap, inside,
    globalsInside.mono grows, relocateGlobals_congr nextMap rename logical.length globals agree globalsInside, paired⟩

/-- Preserve roots from before an earlier method allocation. -/
theorem Preserves.rebase {logical physical middleLogical middlePhysical : Mutable.Heap}
    {rename middleMap : Nat → Nat} {anchors : Nat} {left right : Step State Mutable.Completion}
    (preserved : Preserves middleLogical middlePhysical middleMap anchors left right)
    (agree : ∀ address < logical.length, middleMap address = rename address)
    (grows : logical.length ≤ middleLogical.length) (physicalGrows : physical.length ≤ middlePhysical.length) :
    Preserves logical physical rename anchors left right := by
  obtain ⟨logicalAfter, physicalAfter, nextMap, nextAgree, nextGrows, physicalNextGrows, layout, heap, inside, paired⟩ := preserved
  refine ⟨logicalAfter, physicalAfter, nextMap, ?_, Nat.le_trans grows nextGrows, Nat.le_trans physicalGrows physicalNextGrows,
    layout, heap, inside, paired⟩
  intro address bounded
  exact (nextAgree address (Nat.lt_of_lt_of_le bounded grows)).trans (agree address bounded)


/-- Compose arbitrary finite source traces; the ordinary core obligation remains explicit. -/
theorem reaches_preserves (module : Module) (choices : ChoiceSchedule)
    (logicalAnchors physicalAnchors : Nat) (globals : Mutable.Globals)
    (source : ModuleSource module)
    (coreSteps : ∀ (core : SetCalls.State) (physical : Mutable.Heap) (rename : Nat → Nat),
      ExecutionLayout core.core.heap physical rename → HeapCalls.Relocation.StateWithin core.core →
      GlobalsWithin core.core.heap.length globals →
      SetCalls.Relocation.Preserves core.core.heap physical rename physicalAnchors
        (SetCalls.step module logicalAnchors choices core globals)
        (SetCalls.step module physicalAnchors choices (relocateCore rename physical core) (relocateGlobals rename globals)))
    {first final : State} (before : IteratorCalls.Reaches module logicalAnchors choices globals first final)
    (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout logical physical rename) (heap : StateHeap logical first)
    (inside : StateWithin logical.length first) (globalsInside : GlobalsWithin logical.length globals) :
    ∃ logicalAfter physicalAfter nextMap,
      (∀ address < logical.length, nextMap address = rename address) ∧
      logical.length ≤ logicalAfter.length ∧ physical.length ≤ physicalAfter.length ∧
      ExecutionLayout logicalAfter physicalAfter nextMap ∧ StateHeap logicalAfter final ∧
      StateWithin logicalAfter.length final ∧ GlobalsWithin logicalAfter.length globals ∧
      relocateGlobals nextMap globals = relocateGlobals rename globals ∧
      IteratorCalls.Reaches module physicalAnchors choices (relocateGlobals rename globals)
        (relocateState rename physical physicalAnchors first) (relocateState nextMap physicalAfter physicalAnchors final) := by
  induction before generalizing logical physical rename with
  | refl =>
    exact ⟨logical, physical, rename, fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _,
      layout, heap, inside, globalsInside, rfl, .refl⟩
  | @next state following final transition before ih =>
    have preserved := step_preserves module choices state logical physical rename logicalAnchors physicalAnchors globals
      source layout heap inside globalsInside (by
        intro core resumes same _
        subst state
        have unchanged : core.core.heap = logical := heap
        subst logical
        exact coreSteps core physical rename layout ⟨inside.1, inside.2.1⟩ globalsInside)
    rw [transition] at preserved
    obtain ⟨middleLogical, middlePhysical, middleMap, agree, grows, physicalGrows, middleLayout, middleHeap,
      middleInside, middleGlobals, sameGlobals, moved⟩ := preserved.next globals globalsInside
    obtain ⟨logicalAfter, physicalAfter, nextMap, nextAgree, nextGrows, physicalNextGrows, nextLayout, nextHeap,
      nextInside, nextGlobals, nextSameGlobals, reached⟩ :=
      ih middleLogical middlePhysical middleMap middleLayout middleHeap middleInside middleGlobals
    refine ⟨logicalAfter, physicalAfter, nextMap, ?_, Nat.le_trans grows nextGrows,
      Nat.le_trans physicalGrows physicalNextGrows, nextLayout, nextHeap, nextInside, nextGlobals,
      nextSameGlobals.trans sameGlobals, .next moved ?_⟩
    · intro address bounded
      exact (nextAgree address (Nat.lt_of_lt_of_le bounded grows)).trans (agree address bounded)
    · simpa only [sameGlobals] using reached

end FormalSW.PyAst.IteratorCalls.Relocation
