import lang.py.FormalSW.HeapCalls
import lang.py.FormalSW.Choices

/-! Set traversal extends the ordinary heap interpreter at its unsupported
iterator states. Every unvisited representative can be selected next. Each
schedule produces a deterministic execution; contracts quantify over schedules.
The original set address remains live, so adding a new member invalidates its
iterator on the next read, whereas adding an existing member does not. -/
namespace FormalSW.PyAst.SetCalls
open HeapCalls

structure State where
  core : HeapCalls.State
  choicesUsed : Nat

def liftStep (used : Nat) : Step HeapCalls.State Mutable.Completion → Step State Mutable.Completion
  | .next core => .next ⟨core, used⟩
  | .done outcome => .done outcome
  | .unsupported => .unsupported

def iteratorStep (choices : ChoiceSchedule) (anchors : Nat) (state : State)
    (globals : Mutable.Globals := []) : Step State Mutable.Completion :=
  let ⟨⟨work, stack, heap⟩, used⟩ := state
  match work, stack with
  | .operation (.sumGenerator element ((name, iterable, filters) :: generators) env start)
      [.ref address], stack =>
      match iterable with
      | .call (.name "range") _ => .unsupported
      | _ => match heap[address]? with
          | some (.set items) => .next ⟨⟨.expr start env,
              .sumStart (.setStepLoop name address items items
                (comprehensionFilters filters (sumBody element generators)) [])
                (comprehensionEnv env ((name, iterable, filters) :: generators)) :: stack,
              heap⟩, used⟩
          | _ => .unsupported
  | .operation .sumSequence [.ref address, start], stack =>
      match heap[address]? with
      | some (.set items) => liftStep used
          (sumEnter (globals := globals) anchors
            (.setStepLoop sumItem address items items (sumBody (.name sumItem) []) [])
            (fun _ => none) start stack heap)
      | _ => .unsupported
  | .value (.ref address), .sequence name body otherwise following env :: stack =>
      match heap[address]? with
      | some (.set items) => .next ⟨⟨.block
          (.setStepLoop name address items items body otherwise :: following) env, stack, heap⟩, used⟩
      | _ => .unsupported
  | .block (.setStepLoop name address original remaining body otherwise :: following) env, stack =>
      match heap[address]? with
      | some (.set current) =>
          if current.length != original.length then
            liftStep used (done (globals := globals) anchors heap
              (.error { typeName := "RuntimeError", args := [] }))
          else match remaining with
          | [] => .next ⟨⟨.block (otherwise ++ following) env, stack, heap⟩, used⟩
          | _ :: _ =>
              let index := choices used % remaining.length
              match remaining[index]? with
              | none => .unsupported
              | some item => .next ⟨⟨.block (body ++ [Calls.loopContinuation body
                  (.setStepLoop name address original (remaining.eraseIdx index) body otherwise)] ++ following)
                  (setLocal env name (.scalar item)), stack, heap⟩, used + 1⟩
      | _ => .unsupported
  | _, _ => .unsupported

/-- Every previously supported step is unchanged, including its heap effects. -/
def step (module : Module) (anchors : Nat) (choices : ChoiceSchedule) (state : State)
    (globals : Mutable.Globals := []) : Step State Mutable.Completion :=
  match HeapCalls.step (globals := globals) module anchors state.core with
  | .unsupported => iteratorStep (globals := globals) choices anchors state
  | result => liftStep state.choicesUsed result

def call (module : Module) (name : String) (values : List Mutable.Value)
    (heap : Mutable.Heap) (globals : Mutable.Globals := []) : Mutable.CallFamily :=
  ⟨fun choices => ⟨⟨State, ⟨⟨.operation (.call name) values, [], heap⟩, 0⟩,
    step (globals := globals) module heap.length choices⟩⟩⟩

def evaluate (module : Module) (env : HeapCalls.Env) (expression : Expr)
    (heap : Mutable.Heap) (globals : Mutable.Globals := []) : Mutable.CallFamily :=
  ⟨fun choices => ⟨⟨State, ⟨⟨.expr expression env, [], heap⟩, 0⟩,
    step (globals := globals) module heap.length choices⟩⟩⟩

/-- Every possibly accepted input belongs to the contract domain. Requiring all
choices to return True would incorrectly exclude inputs accepted by some orders.
The separate coverage obligation still quantifies over every choice. -/
def Condition (module : Module) (env : HeapCalls.Env) (expression : Expr)
    (heap : Mutable.Heap) (globals : Mutable.Globals := []) : Prop :=
  ∃ choices finalHeap, ((evaluate (globals := globals) module env expression heap).run choices).Finishes
    ⟨.ok (.scalar (.bool true)), globals, finalHeap, heap.length⟩

variable {globals : Mutable.Globals}

inductive Reaches (choices : ChoiceSchedule) (module : Module) (anchors : Nat) :
    State → State → (globals : Mutable.Globals := []) → Prop where
  | refl {globals : Mutable.Globals} : Reaches choices module anchors state state (globals := globals)
  | next {globals : Mutable.Globals} : step (globals := globals) module anchors choices state = .next following →
      Reaches choices module anchors following final (globals := globals) →
      Reaches choices module anchors state final (globals := globals)

theorem Reaches.trans (first : Reaches choices module anchors a b (globals := globals))
    (rest : Reaches choices module anchors b c (globals := globals)) :
    Reaches choices module anchors a c (globals := globals) := by
  induction first with
  | refl => exact rest
  | next transition _ ih => exact .next transition (ih rest)

theorem Reaches.finishes (first : Reaches choices module anchors a b (globals := globals))
    (rest : Finishes (step (globals := globals) module anchors choices) b outcome) :
    Finishes (step (globals := globals) module anchors choices) a outcome := by
  induction first with
  | refl => exact rest
  | next transition _ ih => exact .next transition (ih rest)

theorem Reaches.of_heap
    (path : HeapCalls.Reaches (globals := globals) module anchors first final)
    (choices : ChoiceSchedule) (used : Nat) :
    Reaches choices module anchors ⟨first, used⟩ ⟨final, used⟩ (globals := globals) := by
  induction path with
  | refl => exact .refl
  | next transition _ ih => exact .next (by simp [step, transition, liftStep]) ih

theorem finishes_of_heap {module : Module} {anchors : Nat} {state : HeapCalls.State}
    (finished : Finishes (HeapCalls.step (globals := globals) module anchors) state outcome)
    (choices : ChoiceSchedule) (used : Nat) :
    Finishes (step (globals := globals) module anchors choices) ⟨state, used⟩ outcome := by
  induction finished with
  | done h => exact .done (by simp [step, h, liftStep])
  | next h _ ih => exact .next (by simp [step, h, liftStep]) ih

/-- Existing deterministic source proofs establish the property for every choice. -/
theorem returns_of_heap
    (h : (HeapCalls.call (globals := globals) module name values heap).Returns) :
    (call (globals := globals) module name values heap).Returns := by
  intro choices
  obtain ⟨value, finalGlobals, finalHeap, anchors, finished⟩ := h
  exact ⟨value, finalGlobals, finalHeap, anchors, finishes_of_heap finished choices 0⟩

end FormalSW.PyAst.SetCalls
