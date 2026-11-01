import lang.py.FormalSW.IteratorRules

/-! Protocol prefixes can run above arbitrary suspended consumers. -/
namespace FormalSW.PyAst.IteratorCalls
open HeapCalls
set_option Elab.async false

def appendResumes (suffix : List Resume) : State → State
  | .running core resumes => .running core (resumes ++ suffix)
  | .completed outcome used resumes => .completed outcome used (resumes ++ suffix)

def appendResumeStep (suffix : List Resume) : Step State Mutable.Completion → Step State Mutable.Completion
  | .next state => .next (appendResumes suffix state)
  | .done outcome => .done outcome
  | .unsupported => .unsupported

theorem enter_append (anchors : Nat) (heap : Mutable.Heap) (used : Nat) (resumes suffix : List Resume)
    (pending : Resume) (method : Mutable.Eval Operation) (globals : Mutable.Globals) :
    enter anchors heap used (resumes ++ suffix) pending method globals =
      appendResumeStep suffix (enter anchors heap used resumes pending method globals) := by
  unfold enter
  split <;> rfl

theorem intercept_append (module : Module) (anchors : Nat) (core : SetCalls.State)
    (resumes suffix : List Resume) (globals : Mutable.Globals) :
    intercept module anchors core (resumes ++ suffix) globals =
      (intercept module anchors core resumes globals).map (appendResumeStep suffix) := by
  unfold intercept
  split <;> first | (split <;> simp [enter_append]) | rfl

theorem lift_append (used : Nat) (resumes suffix : List Resume)
    (transition : Step SetCalls.State Mutable.Completion) :
    lift used (resumes ++ suffix) transition = appendResumeStep suffix (lift used resumes transition) := by
  cases transition <;> rfl

theorem resume_append (module : Module) (completion : Mutable.Completion) (used : Nat)
    (pending : Resume) (rest suffix : List Resume) :
    resume module completion used pending (rest ++ suffix) =
      appendResumeStep suffix (resume module completion used pending rest) := by
  cases pending <;> simp only [resume]
  · split
    · rfl
    · split <;> rfl
  · split
    · rfl
    · split <;> rfl

/-- A nonterminal step never consumes a suffix below its current protocol boundary. -/
theorem step_next_append {module : Module} {anchors : Nat} {choices : ChoiceSchedule}
    {globals : Mutable.Globals} {state following : State}
    (transition : step module anchors choices state globals = .next following)
    (suffix : List Resume) :
    step module anchors choices (appendResumes suffix state) globals = .next (appendResumes suffix following) := by
  have mapped := congrArg (appendResumeStep suffix) transition
  cases state with
  | running core resumes =>
    cases intercepted : intercept module anchors core resumes globals <;>
      simpa only [step, appendResumes, intercept_append, lift_append, intercepted,
        Option.map, appendResumeStep] using mapped
  | completed outcome used resumes =>
    cases resumes with
    | nil => simp [step] at transition
    | cons pending rest =>
      cases outcome with
      | error error => simpa only [step, appendResumes, List.cons_append, appendResumeStep] using mapped
      | ok completion =>
        simpa only [step, appendResumes, List.cons_append, resume_append, appendResumeStep] using mapped

theorem Reaches.append_resumes {module : Module} {anchors : Nat} {choices : ChoiceSchedule}
    {globals : Mutable.Globals} {first final : State}
    (before : Reaches module anchors choices globals first final) (suffix : List Resume) :
    Reaches module anchors choices globals (appendResumes suffix first) (appendResumes suffix final) := by
  induction before with
  | refl => exact .refl
  | next transition _ ih => exact .next (step_next_append transition suffix) ih

theorem enter_not_done (anchors : Nat) (heap : Mutable.Heap) (used : Nat) (resumes : List Resume)
    (pending : Resume) (method : Mutable.Eval Operation) (globals : Mutable.Globals)
    (outcome : Except ExceptionObject Mutable.Completion) :
    enter anchors heap used resumes pending method globals ≠ .done outcome := by
  unfold enter
  split <;> simp

theorem intercept_not_done (module : Module) (anchors : Nat) (core : SetCalls.State)
    (resumes : List Resume) (globals : Mutable.Globals) (outcome : Except ExceptionObject Mutable.Completion) :
    intercept module anchors core resumes globals ≠ some (.done outcome) := by
  unfold intercept
  split <;> first | (split <;> simp [enter_not_done]) | simp

theorem step_done_boundary {module : Module} {anchors : Nat} {choices : ChoiceSchedule}
    {globals : Mutable.Globals} {state : State} {outcome : Except ExceptionObject Mutable.Completion}
    (terminal : step module anchors choices state globals = .done outcome) :
    ∃ used, state = .completed outcome used [] := by
  cases state with
  | running core resumes =>
    simp only [step] at terminal
    cases handled : intercept module anchors core resumes globals with
    | none =>
      rw [handled] at terminal
      cases stepped : SetCalls.step module anchors choices core globals <;> simp [lift, stepped] at terminal
    | some transition =>
      rw [handled] at terminal
      cases terminal
      exact False.elim (intercept_not_done module anchors core resumes globals outcome handled)
  | completed result used resumes =>
    cases resumes with
    | nil => simp only [step, Step.done.injEq] at terminal; exact ⟨used, by rw [terminal]⟩
    | cons pending rest =>
      cases result with
      | error error => simp [step] at terminal
      | ok completion =>
        cases pending <;> simp only [step, resume] at terminal
        all_goals split at terminal <;> (try split at terminal) <;> simp_all [propagate]

/-- Extract the method boundary from a complete iterator execution, including nested calls. -/
theorem completion_of_iterator {module : Module} {anchors : Nat} {choices : ChoiceSchedule}
    {globals : Mutable.Globals} {first : State} {outcome : Except ExceptionObject Mutable.Completion}
    (finished : Finishes (step module anchors choices · globals) first outcome) :
    ∃ used, Reaches module anchors choices globals first (.completed outcome used []) := by
  induction finished with
  | done terminal =>
    obtain ⟨used, rfl⟩ := step_done_boundary terminal
    exact ⟨used, .refl⟩
  | next transition _ ih =>
    obtain ⟨used, rest⟩ := ih
    exact ⟨used, .next transition rest⟩

theorem OperationCompletes.of_iterator {module : Module} {choices : ChoiceSchedule} {used : Nat}
    {operation : Operation} {heap after : Mutable.Heap} {globals : Mutable.Globals}
    {outcome : Except ExceptionObject Mutable.Value}
    (executed : ∀ anchors, Finishes (step module anchors choices · globals)
      (.running ⟨⟨.operation operation [], [], heap⟩, used⟩ [])
      (.ok ⟨outcome, globals, after, anchors⟩)) :
    OperationCompletes module choices used operation heap outcome after globals := by
  intro anchors resumes
  obtain ⟨finalUsed, reached⟩ := completion_of_iterator (executed anchors)
  exact ⟨finalUsed, by simpa only [appendResumes, List.nil_append] using reached.append_resumes resumes⟩

end FormalSW.PyAst.IteratorCalls
