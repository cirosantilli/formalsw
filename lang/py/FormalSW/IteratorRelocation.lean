import lang.py.FormalSW.MachineForDispatch

/-! Saved custom-iterator consumers retain their references and exception boundaries. -/
namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation
set_option Elab.async false

def relocateLoop (rename : Nat → Nat) (loop : Loop) : Loop :=
  ⟨loop.name, loop.body.map (relocateStmt rename), loop.otherwise.map (relocateStmt rename),
    loop.following.map (relocateStmt rename), relocateEnv rename loop.env, loop.stack.map (relocateFrame rename)⟩

def relocateResume (rename : Nat → Nat) : Resume → Resume
  | .acquire loop => .acquire (relocateLoop rename loop)
  | .advance loop iterator => .advance (relocateLoop rename loop) (relocateValue rename iterator)

def relocateCore (rename : Nat → Nat) (physical : Mutable.Heap) (core : SetCalls.State) : SetCalls.State :=
  ⟨HeapCalls.Relocation.relocateState rename physical core.core, core.choicesUsed⟩

def relocateState (rename : Nat → Nat) (physical : Mutable.Heap) (anchors : Nat) : State → State
  | .running core resumes => .running (relocateCore rename physical core) (resumes.map (relocateResume rename))
  | .completed outcome used resumes =>
      .completed (outcome.map (relocateCompletion rename physical anchors)) used (resumes.map (relocateResume rename))

def relocateStep (rename : Nat → Nat) (physical : Mutable.Heap) (anchors : Nat) :
    Step State Mutable.Completion → Step State Mutable.Completion
  | .next state => .next (relocateState rename physical anchors state)
  | .done outcome => .done (outcome.map (relocateCompletion rename physical anchors))
  | .unsupported => .unsupported

def LoopWithin (limit : Nat) (loop : Loop) : Prop :=
  EnvWithin limit loop.env ∧
  (∀ statement ∈ loop.body, StmtWithin limit statement) ∧
  (∀ statement ∈ loop.otherwise, StmtWithin limit statement) ∧
  (∀ statement ∈ loop.following, StmtWithin limit statement) ∧
  (∀ frame ∈ loop.stack, FrameWithin limit frame)

def ResumeWithin (limit : Nat) : Resume → Prop
  | .acquire loop => LoopWithin limit loop
  | .advance loop iterator => LoopWithin limit loop ∧ iterator.edge.Within limit

/-- Bounds on saved references; the limit is supplied by the current runtime layout. -/
def StateWithin (limit : Nat) : State → Prop
  | .running core resumes =>
      WorkWithin limit core.core.work ∧ (∀ frame ∈ core.core.stack, FrameWithin limit frame) ∧
      (∀ pending ∈ resumes, ResumeWithin limit pending)
  | .completed (.ok completion) _ resumes =>
      GlobalsWithin limit completion.globals ∧
      (∀ value, completion.outcome = .ok value → value.edge.Within limit) ∧
      (∀ pending ∈ resumes, ResumeWithin limit pending)
  | .completed (.error _) _ resumes => ∀ pending ∈ resumes, ResumeWithin limit pending

def StepWithin (limit : Nat) : Step State Mutable.Completion → Prop
  | .next state => StateWithin limit state
  | .done (.ok completion) => GlobalsWithin limit completion.globals ∧
      ∀ value, completion.outcome = .ok value → value.edge.Within limit
  | .done (.error _) | .unsupported => True

theorem loopCode_relocates (rename : Nat → Nat) (loop : Loop) (iterator : Mutable.Value) :
    loopCode (relocateLoop rename loop) (relocateValue rename iterator) =
      relocateStmt rename (loopCode loop iterator) := by
  simp only [loopCode, relocateLoop, relocateStmt, sequenceSource_relocate]

theorem loopCode_within (limit : Nat) (loop : Loop) (iterator : Mutable.Value)
    (saved : LoopWithin limit loop) (inside : iterator.edge.Within limit) :
    StmtWithin limit (loopCode loop iterator) := by
  simp only [loopCode, StmtWithin]
  exact ⟨sequenceSource_within limit iterator inside, saved.2.1, saved.2.2.1⟩

theorem relocateLoop_congr (left right : Nat → Nat) (limit : Nat) (loop : Loop)
    (agree : ∀ address < limit, left address = right address) (inside : LoopWithin limit loop) :
    relocateLoop left loop = relocateLoop right loop := by
  have body := List.map_congr_left (fun statement member => relocateStmt_congr left right limit statement agree (inside.2.1 statement member))
  have otherwise := List.map_congr_left (fun statement member => relocateStmt_congr left right limit statement agree (inside.2.2.1 statement member))
  have following := List.map_congr_left (fun statement member => relocateStmt_congr left right limit statement agree (inside.2.2.2.1 statement member))
  simp only [relocateLoop, body, otherwise, following, relocateEnv_congr left right limit loop.env agree inside.1,
    relocateStack_congr left right limit loop.stack agree inside.2.2.2.2]

theorem relocateResume_congr (left right : Nat → Nat) (limit : Nat) (pending : Resume)
    (agree : ∀ address < limit, left address = right address) (inside : ResumeWithin limit pending) :
    relocateResume left pending = relocateResume right pending := by
  cases pending with
  | acquire loop => exact congrArg Resume.acquire (relocateLoop_congr left right limit loop agree inside)
  | advance loop iterator =>
    simp only [relocateResume, relocateLoop_congr left right limit loop agree inside.1,
      relocateValue_congr left right limit iterator agree inside.2]

theorem LoopWithin.mono {before after : Nat} {loop : Loop} (inside : LoopWithin before loop)
    (larger : before ≤ after) : LoopWithin after loop :=
  ⟨inside.1.mono larger, fun statement member => (inside.2.1 statement member).mono larger,
    fun statement member => (inside.2.2.1 statement member).mono larger,
    fun statement member => (inside.2.2.2.1 statement member).mono larger,
    fun frame member => (inside.2.2.2.2 frame member).mono larger⟩

theorem ResumeWithin.mono {before after : Nat} {pending : Resume} (inside : ResumeWithin before pending)
    (larger : before ≤ after) : ResumeWithin after pending := by
  cases pending with
  | acquire => exact LoopWithin.mono inside larger
  | advance => exact ⟨LoopWithin.mono inside.1 larger, valueWithin_mono before after _ larger inside.2⟩

theorem propagate_relocates (rename : Nat → Nat) (physical : Mutable.Heap) (anchors : Nat)
    (loop : Loop) (completion : Mutable.Completion) (used : Nat) (resumes : List Resume) :
    propagate (relocateLoop rename loop) (relocateCompletion rename physical anchors completion)
        used (resumes.map (relocateResume rename)) =
      relocateStep rename physical anchors (propagate loop completion used resumes) := by
  rcases completion with ⟨outcome, globals, heap, originalAnchors⟩
  cases outcome <;> simp [propagate, relocateLoop, relocateStep, relocateState, relocateCompletion,
    Except.map, Function.comp_def, relocateFrame_inGenerator]

theorem nextMethod_keeps_heap (module : Module) (heap after : Mutable.Heap) (value : Mutable.Value)
    (outcome : Except ExceptionObject (Option Operation)) (inside : value.edge.Within heap.length)
    (executed : ProtocolCalls.nextMethod module value heap = some (outcome, after)) : after = heap := by
  have same := nextMethod_relocates (RuntimeLayout.refl heap) module value inside
  simp only [relocateValue_id, executed, Option.map_some] at same
  exact congrArg Prod.snd (Option.some.inj same)

theorem iterFinish_relocates (module : Module) (completion : Mutable.Completion) (physical : Mutable.Heap)
    (rename : Nat → Nat) (anchors : Nat) (layout : RuntimeLayout completion.heap physical rename)
    (inside : ∀ value, completion.outcome = .ok value → value.edge.Within completion.heap.length) :
    ProtocolCalls.iterFinish module (relocateCompletion rename physical anchors completion) =
      (ProtocolCalls.iterFinish module completion).map (relocateCompletion rename physical anchors) := by
  rcases completion with ⟨outcome, globals, logical, originalAnchors⟩
  cases outcome with
  | error exception => rfl
  | ok value =>
    have bounded := inside value rfl
    have paired := nextMethod_relocates layout module value bounded
    cases tested : ProtocolCalls.nextMethod module value logical with
    | none => simp [ProtocolCalls.iterFinish, relocateCompletion, paired, tested, Except.map]
    | some pair =>
      rcases pair with ⟨result, after⟩
      have unchanged := nextMethod_keeps_heap module logical after value result bounded tested
      subst after
      cases result with
      | error exception => simp [ProtocolCalls.iterFinish, relocateCompletion, paired, tested, Except.map]
      | ok method => cases method <;> simp [ProtocolCalls.iterFinish, relocateCompletion, paired, tested, Except.map]

theorem iterFinish_effect (module : Module) (completion checked : Mutable.Completion)
    (inside : ∀ value, completion.outcome = .ok value → value.edge.Within completion.heap.length)
    (finished : ProtocolCalls.iterFinish module completion = some checked) :
    checked.heap = completion.heap ∧ checked.globals = completion.globals ∧
      ∀ value, checked.outcome = .ok value → completion.outcome = .ok value := by
  rcases completion with ⟨outcome, globals, heap, anchors⟩
  cases outcome with
  | error exception =>
    simp only [ProtocolCalls.iterFinish, Option.some.injEq] at finished
    subst checked
    exact ⟨rfl, rfl, fun _ same => same⟩
  | ok value =>
    cases tested : ProtocolCalls.nextMethod module value heap with
    | none => simp [ProtocolCalls.iterFinish, tested] at finished
    | some pair =>
      rcases pair with ⟨result, after⟩
      have unchanged := nextMethod_keeps_heap module heap after value result (inside value rfl) tested
      subst after
      cases result with
      | error exception =>
        simp only [ProtocolCalls.iterFinish, tested, Option.some.injEq] at finished
        subst checked
        exact ⟨rfl, rfl, by intro _ impossible; cases impossible⟩
      | ok method =>
        cases method <;> simp only [ProtocolCalls.iterFinish, tested, Option.some.injEq] at finished <;> subst checked
        · exact ⟨rfl, rfl, by intro _ impossible; cases impossible⟩
        · exact ⟨rfl, rfl, fun _ same => same⟩

theorem resume_relocates (module : Module) (completion : Mutable.Completion) (physical : Mutable.Heap)
    (rename : Nat → Nat) (anchors used : Nat) (pending : Resume) (rest : List Resume)
    (layout : RuntimeLayout completion.heap physical rename)
    (inside : ∀ value, completion.outcome = .ok value → value.edge.Within completion.heap.length) :
    resume module (relocateCompletion rename physical anchors completion) used (relocateResume rename pending)
        (rest.map (relocateResume rename)) =
      relocateStep rename physical anchors (resume module completion used pending rest) := by
  cases pending with
  | acquire loop =>
    have paired := iterFinish_relocates module completion physical rename anchors layout inside
    simp only [relocateResume, resume, paired]
    cases tested : ProtocolCalls.iterFinish module completion with
    | none => simp [relocateStep]
    | some checked =>
      rcases checked with ⟨outcome, globals, heap, originalAnchors⟩
      cases outcome <;>
        simp [relocateCompletion, relocateLoop, relocateStep, relocateState, relocateCore,
          HeapCalls.Relocation.relocateState, relocateWork, relocateStmt, loopCode, sequenceSource_relocate,
          propagate, Except.map, Function.comp_def, relocateFrame_inGenerator]
  | advance loop iterator =>
    rcases completion with ⟨outcome, globals, heap, originalAnchors⟩
    cases outcome with
    | ok value =>
      simp [relocateResume, resume, relocateCompletion, relocateLoop, relocateStep, relocateState, relocateCore,
        HeapCalls.Relocation.relocateState, relocateWork, relocateEnv_set,
        ← loopContinuation_relocate, List.map_append, relocateStmt, loopCode, sequenceSource_relocate, Except.map]
    | error exception =>
      by_cases exhausted : exception.typeName = "StopIteration" <;>
        simp [relocateResume, resume, relocateCompletion, exhausted, propagate, relocateLoop, relocateStep,
          relocateState, relocateCore, HeapCalls.Relocation.relocateState, relocateWork, Function.comp_def, relocateFrame_inGenerator, Except.map]

theorem step_completed_relocates (module : Module) (choices : ChoiceSchedule)
    (completion : Mutable.Completion) (physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors used : Nat) (resumes : List Resume)
    (layout : RuntimeLayout completion.heap physical rename)
    (inside : ∀ value, completion.outcome = .ok value → value.edge.Within completion.heap.length) :
    IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.completed (.ok completion) used resumes)) =
      relocateStep rename physical physicalAnchors
        (IteratorCalls.step module logicalAnchors choices (.completed (.ok completion) used resumes)) := by
  cases resumes with
  | nil => rfl
  | cons pending rest => exact resume_relocates module completion physical rename physicalAnchors used pending rest layout inside

theorem step_completed_error_relocates (module : Module) (choices : ChoiceSchedule)
    (exception : ExceptionObject) (physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors used : Nat) (resumes : List Resume) :
    IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.completed (.error exception) used resumes)) =
      relocateStep rename physical physicalAnchors
        (IteratorCalls.step module logicalAnchors choices (.completed (.error exception) used resumes)) := by
  cases resumes <;> rfl


theorem propagate_within (limit : Nat) (loop : Loop) (completion : Mutable.Completion)
    (used : Nat) (rest : List Resume)
    (globalsInside : GlobalsWithin limit completion.globals)
    (valueInside : ∀ value, completion.outcome = .ok value → value.edge.Within limit)
    (restInside : ∀ pending ∈ rest, ResumeWithin limit pending) :
    StepWithin limit (propagate loop completion used rest) := by
  rcases completion with ⟨outcome, globals, heap, anchors⟩
  cases outcome with
  | error exception => exact ⟨globalsInside, (by intro _ impossible; cases impossible), restInside⟩
  | ok value => exact ⟨globalsInside, valueInside, restInside⟩

theorem resume_within (module : Module) (completion : Mutable.Completion) (used : Nat)
    (pending : Resume) (rest : List Resume)
    (inside : CompletionWithin completion) (saved : ResumeWithin completion.heap.length pending)
    (restInside : ∀ pending ∈ rest, ResumeWithin completion.heap.length pending) :
    StepWithin completion.heap.length (resume module completion used pending rest) := by
  cases pending with
  | acquire loop =>
    cases tested : ProtocolCalls.iterFinish module completion with
    | none => simp [resume, tested, StepWithin]
    | some checked =>
      have effect := iterFinish_effect module completion checked inside.2 tested
      have globalsInside : GlobalsWithin completion.heap.length checked.globals := effect.2.1 ▸ inside.1
      have valueInside : ∀ value, checked.outcome = .ok value → value.edge.Within completion.heap.length :=
        fun value success => inside.2 value (effect.2.2 value success)
      cases outcome : checked.outcome with
      | error exception =>
        simp only [resume, tested, outcome]
        exact propagate_within completion.heap.length loop checked used rest globalsInside valueInside restInside
      | ok iterator =>
        simp only [resume, tested, outcome, StepWithin, StateWithin, WorkWithin]
        refine ⟨⟨saved.1, ?_⟩, saved.2.2.2.2, restInside⟩
        intro statement member
        rcases List.mem_cons.mp member with rfl | member
        · exact loopCode_within completion.heap.length loop iterator saved (valueInside iterator outcome)
        · exact saved.2.2.2.1 statement member
  | advance loop iterator =>
    cases outcome : completion.outcome with
    | ok value =>
      simp only [resume, outcome, StepWithin, StateWithin, WorkWithin]
      refine ⟨⟨saved.1.1.setLocal loop.name value (inside.2 value outcome), ?_⟩, saved.1.2.2.2.2, restInside⟩
      intro statement member
      rcases List.mem_append.mp member with member | member
      · rcases List.mem_append.mp member with member | member
        · exact saved.1.2.1 statement member
        · have same := List.mem_singleton.mp member
          subst statement
          exact loopContinuation_within completion.heap.length loop.body (loopCode loop iterator)
            (loopCode_within completion.heap.length loop iterator saved.1 saved.2)
      · exact saved.1.2.2.2.1 statement member
    | error exception =>
      by_cases exhausted : exception.typeName = "StopIteration"
      · simp only [resume, outcome, exhausted, if_true, StepWithin, StateWithin, WorkWithin]
        exact ⟨⟨saved.1.1, fun statement member =>
          (List.mem_append.mp member).elim (saved.1.2.2.1 statement) (saved.1.2.2.2.1 statement)⟩,
          saved.1.2.2.2.2, restInside⟩
      · simp only [resume, outcome, exhausted, if_false]
        exact propagate_within completion.heap.length loop completion used rest inside.1 inside.2 restInside

theorem step_completed_within (module : Module) (choices : ChoiceSchedule)
    (completion : Mutable.Completion) (anchors used : Nat) (resumes : List Resume)
    (inside : CompletionWithin completion)
    (saved : ∀ pending ∈ resumes, ResumeWithin completion.heap.length pending) :
    StepWithin completion.heap.length (IteratorCalls.step module anchors choices (.completed (.ok completion) used resumes)) := by
  cases resumes with
  | nil => exact inside
  | cons pending rest =>
    exact resume_within module completion used pending rest inside (saved pending (by simp))
      (fun pending member => saved pending (List.mem_cons_of_mem _ member))

theorem step_completed_error_within (module : Module) (choices : ChoiceSchedule)
    (exception : ExceptionObject) (limit anchors used : Nat) (resumes : List Resume)
    (saved : ∀ pending ∈ resumes, ResumeWithin limit pending) :
    StepWithin limit (IteratorCalls.step module anchors choices (.completed (.error exception) used resumes)) := by
  cases resumes with
  | nil => trivial
  | cons pending rest => exact fun pending member => saved pending (List.mem_cons_of_mem _ member)

theorem relocateCompletion_congr (left right : Nat → Nat) (limit : Nat)
    (completion : Mutable.Completion) (physical : Mutable.Heap) (anchors : Nat)
    (agree : ∀ address < limit, left address = right address)
    (globalsInside : GlobalsWithin limit completion.globals)
    (valueInside : ∀ value, completion.outcome = .ok value → value.edge.Within limit) :
    relocateCompletion left physical anchors completion = relocateCompletion right physical anchors completion := by
  rcases completion with ⟨outcome, globals, heap, originalAnchors⟩
  have moved := relocateGlobals_congr left right limit globals agree globalsInside
  cases outcome with
  | error exception => simp only [relocateCompletion, Except.map, moved]
  | ok value =>
    simp only [relocateCompletion, Except.map, moved,
      relocateValue_congr left right limit value agree (valueInside value rfl)]

theorem relocateState_congr (left right : Nat → Nat) (limit : Nat) (state : State)
    (physical : Mutable.Heap) (anchors : Nat) (agree : ∀ address < limit, left address = right address)
    (inside : StateWithin limit state) :
    relocateState left physical anchors state = relocateState right physical anchors state := by
  cases state with
  | running core resumes =>
    have work := relocateWork_congr left right limit core.core.work agree inside.1
    have stack := relocateStack_congr left right limit core.core.stack agree inside.2.1
    have pending := List.map_congr_left (fun pending member => relocateResume_congr left right limit pending agree (inside.2.2 pending member))
    simp only [relocateState, relocateCore, HeapCalls.Relocation.relocateState, work, stack, pending]
  | completed outcome used resumes =>
    cases outcome with
    | error exception =>
      have pending := List.map_congr_left (fun pending member => relocateResume_congr left right limit pending agree (inside pending member))
      simp only [relocateState, Except.map, pending]
    | ok completion =>
      have pending := List.map_congr_left (fun pending member => relocateResume_congr left right limit pending agree (inside.2.2 pending member))
      simp only [relocateState, Except.map, pending,
        relocateCompletion_congr left right limit completion physical anchors agree inside.1 inside.2.1]

theorem StateWithin.mono {before after : Nat} {state : State} (inside : StateWithin before state)
    (larger : before ≤ after) : StateWithin after state := by
  cases state with
  | running core resumes =>
    exact ⟨inside.1.mono larger, fun frame member => (inside.2.1 frame member).mono larger,
      fun pending member => ResumeWithin.mono (inside.2.2 pending member) larger⟩
  | completed outcome used resumes =>
    cases outcome with
    | error exception => exact fun pending member => ResumeWithin.mono (inside pending member) larger
    | ok completion =>
      exact ⟨inside.1.mono larger, fun value success => valueWithin_mono before after value larger (inside.2.1 value success),
        fun pending member => ResumeWithin.mono (inside.2.2 pending member) larger⟩

end FormalSW.PyAst.IteratorCalls.Relocation
