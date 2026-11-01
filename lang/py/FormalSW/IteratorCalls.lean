import lang.py.FormalSW.ProtocolCalls
import lang.py.FormalSW.SetCalls

/-! Source named-target for-loops over plain class instances retain the acquired iterator and
execute its methods in the same interpreter, including nested custom loops.
Only exhaustion from the advancement call is consumed by the loop. -/
namespace FormalSW.PyAst.IteratorCalls
open HeapCalls
set_option Elab.async false

structure Loop where
  name : String
  body : List Stmt
  otherwise : List Stmt
  following : List Stmt
  env : HeapCalls.Env
  stack : List HeapCalls.Frame

inductive Resume where
  | acquire (loop : Loop)
  | advance (loop : Loop) (iterator : Mutable.Value)

inductive State where
  | running (core : SetCalls.State) (resumes : List Resume)
  | completed (outcome : Except ExceptionObject Mutable.Completion)
      (used : Nat) (resumes : List Resume)

def isInstance (heap : Mutable.Heap) : Mutable.Value → Bool
  | .ref address => match heap[address]? with
      | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) => true
      | _ => false
  | .scalar _ => false

def loopCode (loop : Loop) (iterator : Mutable.Value) : Stmt :=
  .sequenceStepLoop loop.name (sequenceSource iterator) 0 loop.body loop.otherwise

def lift (used : Nat) (resumes : List Resume) :
    Step SetCalls.State Mutable.Completion → Step State Mutable.Completion
  | .next core => .next (.running core resumes)
  | .done outcome => .next (.completed outcome used resumes)
  | .unsupported => .unsupported

/-- Preserve the caller's generator exception boundary after a protocol method exits. -/
def propagate (loop : Loop) (completion : Mutable.Completion)
    (used : Nat) (resumes : List Resume) : Step State Mutable.Completion :=
  .next (.completed (.ok { completion with outcome := match completion.outcome with
    | .error error => .error (Calls.generatorException (loop.stack.any Frame.inGenerator) error)
    | .ok value => .ok value }) used resumes)

def resume (module : Module) (completion : Mutable.Completion) (used : Nat)
    (pending : Resume) (rest : List Resume) : Step State Mutable.Completion :=
  match pending with
  | .acquire loop =>
      match ProtocolCalls.iterFinish module completion with
      | none => .unsupported
      | some checked => match checked.outcome with
          | .error _ => propagate loop checked used rest
          | .ok iterator => .next (.running
              ⟨⟨.block (loopCode loop iterator :: loop.following) loop.env,
                loop.stack, checked.heap⟩, used⟩ rest)
  | .advance loop iterator =>
      match completion.outcome with
      | .ok value => .next (.running
          ⟨⟨.block (loop.body ++ [Calls.loopContinuation loop.body (loopCode loop iterator)]
              ++ loop.following) (setLocal loop.env loop.name value),
            loop.stack, completion.heap⟩, used⟩ rest)
      | .error error =>
          if error.typeName = "StopIteration" then .next (.running
            ⟨⟨.block (loop.otherwise ++ loop.following) loop.env,
              loop.stack, completion.heap⟩, used⟩ rest)
          else propagate loop completion used rest

/-- Save the consuming loop separately, so it cannot catch exceptions from its own body. -/
def enter (anchors : Nat) (heap : Mutable.Heap) (used : Nat) (resumes : List Resume)
    (pending : Resume) (method : Mutable.Eval Operation) (globals : Mutable.Globals) :
    Step State Mutable.Completion :=
  match method heap with
  | none => .unsupported
  | some (.error error, after) =>
      .next (.completed (.ok ⟨.error error, globals, after, anchors⟩) used (pending :: resumes))
  | some (.ok operation, after) =>
      .next (.running ⟨⟨.operation operation [], [], after⟩, used⟩ (pending :: resumes))

/-- Intercept instance loops before the sequence-only core would report TypeError. -/
def intercept (module : Module) (anchors : Nat) (core : SetCalls.State)
    (resumes : List Resume) (globals : Mutable.Globals) :
    Option (Step State Mutable.Completion) :=
  let ⟨⟨work, stack, heap⟩, used⟩ := core
  match work, stack with
  | .value receiver, .sequence name body otherwise following env :: stack =>
      if isInstance heap receiver then
        some (enter anchors heap used resumes
          (.acquire ⟨name, body, otherwise, following, env, stack⟩)
          (ProtocolCalls.iterMethod module receiver) globals)
      else none
  | .block (.sequenceStepLoop name source _ body otherwise :: following) env, stack =>
      let iterator := sequenceValue source
      if isInstance heap iterator then
        some (enter anchors heap used resumes
          (.advance ⟨name, body, otherwise, following, env, stack⟩ iterator)
          (do match ← ProtocolCalls.nextMethod module iterator with
              | some operation => pure operation
              | none => Mutable.error "TypeError") globals)
      else none
  | _, _ => none

def step (module : Module) (anchors : Nat) (choices : ChoiceSchedule) (state : State)
    (globals : Mutable.Globals := []) : Step State Mutable.Completion :=
  match state with
  | .running core resumes =>
      match intercept module anchors core resumes globals with
      | some transition => transition
      | none => lift core.choicesUsed resumes
          (SetCalls.step (globals := globals) module anchors choices core)
  | .completed outcome used resumes => match resumes with
      | [] => .done outcome
      | pending :: rest => match outcome with
          | .error error => .next (.completed (.error error) used rest)
          | .ok completion => resume module completion used pending rest

def call (module : Module) (name : String) (values : List Mutable.Value)
    (heap : Mutable.Heap) (globals : Mutable.Globals := []) : Mutable.CallFamily :=
  ⟨fun choices => ⟨⟨State, .running ⟨⟨.operation (.call name) values, [], heap⟩, 0⟩ [],
    step (globals := globals) module heap.length choices⟩⟩⟩

inductive Reaches (module : Module) (anchors : Nat) (choices : ChoiceSchedule)
    (globals : Mutable.Globals) : State → State → Prop where
  | refl {state : State} : Reaches module anchors choices globals state state
  | next {state following final : State} :
      step module anchors choices state globals = .next following →
      Reaches module anchors choices globals following final →
      Reaches module anchors choices globals state final

theorem Reaches.trans {module : Module} {anchors : Nat} {choices : ChoiceSchedule}
    {globals : Mutable.Globals} {first middle final : State}
    (before : Reaches module anchors choices globals first middle)
    (after : Reaches module anchors choices globals middle final) :
    Reaches module anchors choices globals first final := by
  induction before with
  | refl => exact after
  | next transition _ ih => exact .next transition (ih after)

theorem Reaches.finishes {module : Module} {anchors : Nat} {choices : ChoiceSchedule}
    {globals : Mutable.Globals} {first final : State}
    {outcome : Except ExceptionObject Mutable.Completion}
    (before : Reaches module anchors choices globals first final)
    (after : Finishes (step module anchors choices · globals) final outcome) :
    Finishes (step module anchors choices · globals) first outcome := by
  induction before with
  | refl => exact after
  | next transition _ ih => exact .next transition (ih after)

/-- Compose a complete acquisition, including its actual source method execution,
with the loop that retains the returned iterator. -/
theorem acquired {module : Module} {anchors used : Nat} {choices : ChoiceSchedule}
    {globals : Mutable.Globals} {first : State} {loop : Loop} {resumes : List Resume}
    {heap : Mutable.Heap} {iterator : Mutable.Value} {operation : Operation}
    (before : Reaches module anchors choices globals first
      (.completed (.ok ⟨.ok iterator, globals, heap, anchors⟩) used (.acquire loop :: resumes)))
    (valid : ProtocolCalls.nextMethod module iterator heap =
      some (.ok (some operation), heap)) :
    Reaches module anchors choices globals first (.running
      ⟨⟨.block (loopCode loop iterator :: loop.following) loop.env, loop.stack, heap⟩, used⟩
      resumes) := by
  apply before.trans
  exact .next (by simp [step, resume, ProtocolCalls.iterFinish, valid]) .refl

/-- A yielded value runs the body with a saved iterator, independent of rebinding the iterable. -/
theorem advanced {module : Module} {anchors used : Nat} {choices : ChoiceSchedule}
    {globals : Mutable.Globals} {first : State} {loop : Loop} {resumes : List Resume}
    {heap : Mutable.Heap} {iterator value : Mutable.Value}
    (before : Reaches module anchors choices globals first
      (.completed (.ok ⟨.ok value, globals, heap, anchors⟩) used
        (.advance loop iterator :: resumes))) :
    Reaches module anchors choices globals first (.running
      ⟨⟨.block (loop.body ++ [Calls.loopContinuation loop.body (loopCode loop iterator)]
          ++ loop.following) (setLocal loop.env loop.name value), loop.stack, heap⟩, used⟩
      resumes) :=
  before.trans (.next rfl .refl)

/-- Exhaustion keeps next's final heap writes and executes the loop's else branch. -/
theorem exhausted {module : Module} {anchors used : Nat} {choices : ChoiceSchedule}
    {globals : Mutable.Globals} {first : State} {loop : Loop} {resumes : List Resume}
    {heap : Mutable.Heap} {iterator : Mutable.Value} {args : List Constant}
    (before : Reaches module anchors choices globals first
      (.completed (.ok ⟨.error ⟨"StopIteration", args⟩, globals, heap, anchors⟩) used
        (.advance loop iterator :: resumes))) :
    Reaches module anchors choices globals first (.running
      ⟨⟨.block (loop.otherwise ++ loop.following) loop.env, loop.stack, heap⟩, used⟩ resumes) :=
  before.trans (.next rfl .refl)


/-- Instance iteration is the precise place where the older sequence runner
reported TypeError, irrespective of the instance's protocol methods. -/
theorem sequence_instance {heap : Mutable.Heap} {value : Mutable.Value}
    (hasInstance : isInstance heap value = true) :
    Mutable.sequence value heap =
      some (.error { typeName := "TypeError", args := [] }, heap) := by
  cases value with
  | scalar value => simp [isInstance] at hasInstance
  | ref address =>
      cases found : heap[address]? with
      | none => simp [isInstance, found] at hasInstance
      | some object =>
          cases object <;> simp_all [isInstance, Mutable.sequence, Mutable.error]

/-- Ordinary core transitions can be reused without stepping through protocol machinery. -/
theorem core_next {module : Module} {anchors : Nat} {choices : ChoiceSchedule}
    {globals : Mutable.Globals} {core following : SetCalls.State} {resumes : List Resume}
    (ordinary : intercept module anchors core resumes globals = none)
    (transition : SetCalls.step module anchors choices core globals = .next following) :
    step module anchors choices (.running core resumes) globals =
      .next (.running following resumes) := by
  simp [step, ordinary, transition, lift]

/-- A completed source method is delivered to exactly its own pending protocol call. -/
theorem core_done {module : Module} {anchors : Nat} {choices : ChoiceSchedule}
    {globals : Mutable.Globals} {core : SetCalls.State} {resumes : List Resume}
    {outcome : Except ExceptionObject Mutable.Completion}
    (ordinary : intercept module anchors core resumes globals = none)
    (transition : SetCalls.step module anchors choices core globals = .done outcome) :
    step module anchors choices (.running core resumes) globals =
      .next (.completed outcome core.choicesUsed resumes) := by
  simp [step, ordinary, transition, lift]

end FormalSW.PyAst.IteratorCalls
