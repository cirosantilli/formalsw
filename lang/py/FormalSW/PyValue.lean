import lang.py.FormalSW.Concurrent
import lang.py.FormalSW.ParallelLiveness

namespace FormalSW.PyAst

/-- Values at the Python/Lean boundary. Lists are materialized as shared mutable
arrays when passed to a trial; theorem variables describe their initial contents. -/
inductive PyValue where
  | int (value : Int)
  | bool (value : Bool)
  | string (value : String)
  | none
  | list (values : List PyValue)
  | object (className : String)
  deriving Repr, BEq

namespace PyValue

def typeName : PyValue → String
  | .int _ => "int" | .bool _ => "bool" | .string _ => "str"
  | .none => "NoneType" | .list _ => "list" | .object _ => "object"

def asInt : PyValue → Option Int
  | .int n => some n | _ => Option.none

def asInts : PyValue → Option (List Int)
  | .list values => values.mapM asInt | _ => Option.none

def length : PyValue → Option PyValue
  | .list values => some (.int values.length)
  | .string value => some (.int value.length)
  | _ => Option.none

def typeIs (value : PyValue) (name : String) : Option PyValue :=
  some (.bool (value.typeName == name))

def compare (op : CmpOp) (left right : PyValue) : Option PyValue := do
  match op with
  | .eq => return .bool (left == right)
  | .notEq => return .bool (left != right)
  | _ =>
      let left ← left.asInt
      let right ← right.asInt
      return .bool (match op with
        | .lt => left < right | .ltE => left ≤ right
        | .gt => left > right | .gtE => left ≥ right | _ => false)

/-- Short-circuit before evaluating the right-hand expression. -/
def andThen (left : Option PyValue) (right : Unit → Option PyValue) : Option PyValue := do
  match ← left with
  | .bool true => right ()
  | .bool false => some (.bool false)
  | _ => Option.none

def all (predicate : PyValue → Option PyValue) : PyValue → Option PyValue
  | .list values => values.foldr (fun value rest => andThen (predicate value) (fun _ => rest)) (some (.bool true))
  | _ => Option.none

def IsTrue (value : Option PyValue) : Prop := value = some (.bool true)

@[simp] theorem asInt_int (n : Int) : asInt (.int n) = some n := rfl
@[simp] theorem asInts_ints (values : List Int) : asInts (.list (values.map .int)) = some values := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
      simp only [asInts, List.map_cons, List.mapM_cons, asInt] at *
      rw [ih]
      rfl

@[simp] theorem andThen_true (left : Option PyValue) (right : Unit → Option PyValue) :
    andThen left right = some (.bool true) ↔ left = some (.bool true) ∧ right () = some (.bool true) := by
  cases left with
  | none => simp [andThen]
  | some value =>
      cases value <;> simp [andThen]
      case bool value => cases value <;> simp

@[simp] theorem typeIs_int (value : PyValue) :
    typeIs value "int" = some (.bool true) ↔ ∃ n, value = .int n := by
  cases value <;> simp [typeIs, typeName]

@[simp] theorem typeIs_list (value : PyValue) :
    typeIs value "list" = some (.bool true) ↔ ∃ values, value = .list values := by
  cases value <;> simp [typeIs, typeName]

/-- Type guards justify the conversion; annotations never supply this fact. -/
theorem ints_of_all (values : List PyValue)
    (guard : all (fun value => typeIs value "int") (.list values) = some (.bool true)) :
    ∃ (integers : List Int), values = integers.map .int := by
  induction values with
  | nil => exact ⟨[], rfl⟩
  | cons value rest ih =>
      cases value <;> simp [all, andThen, typeIs, typeName, List.foldr] at guard
      case int n =>
        obtain ⟨integers, rfl⟩ := ih guard
        exact ⟨n :: integers, rfl⟩

end PyValue

/- Unbounded mutex execution using the same per-operation interpreter as
Parallel. Waiting workers are blocked at their common acquire; the current
owner advances one actual Python operation at a time. -/
namespace Mutex

inductive Ensures (post : SharedState → Prop) : List ParallelWorker → Option ParallelWorker → SharedState → Prop where
  | done : post state → Ensures post [] none state
  | acquire : pending ≠ [] →
      (∀ before worker after, pending = before ++ worker :: after →
        Ensures post (before ++ after) (some worker) state) → Ensures post pending none state
  | step : parallelStep state worker = some (.ok (nextState, nextWorker)) →
      Ensures post pending (some nextWorker) nextState → Ensures post pending (some worker) state
  | release : worker.todo = [] → Ensures post pending none state → Ensures post pending (some worker) state

def executeFuel : Nat → ParallelWorker → SharedState → Option SharedState
  | fuel, worker, state =>
      if worker.todo = [] then some state
      else match fuel with
        | 0 => none
        | fuel + 1 => do
            let .ok (next, worker) ← parallelStep state worker | none
            executeFuel fuel worker next

def execute (ops : List ParallelOp) (env : SharedEnv) (state : SharedState) : Option SharedState :=
  executeFuel ops.length ⟨ops, env⟩ state

theorem withinFuel (fuel : Nat) (worker : ParallelWorker) (state final : SharedState)
    (execution : executeFuel fuel worker state = some final)
    (rest : Ensures post pending none final) : Ensures post pending (some worker) state := by
  induction fuel generalizing worker state with
  | zero =>
      by_cases done : worker.todo = []
      · simp [executeFuel, done] at execution
        subst final; exact .release done rest
      · simp [executeFuel, done] at execution
  | succ fuel ih =>
      by_cases done : worker.todo = []
      · simp [executeFuel, done] at execution
        subst final; exact .release done rest
      · simp only [executeFuel, done, ↓reduceIte] at execution
        cases h : parallelStep state worker with
        | none => simp [h] at execution
        | some outcome =>
            cases outcome with
            | error error => simp [h] at execution
            | ok pair =>
                rcases pair with ⟨next, nextWorker⟩
                exact .step h (ih nextWorker next (by simpa [h] using execution))

theorem within (ops : List ParallelOp) (env : SharedEnv) (state final : SharedState)
    (execution : execute ops env state = some final)
    (rest : Ensures post pending none final) : Ensures post pending (some ⟨ops, env⟩) state :=
  withinFuel ops.length ⟨ops, env⟩ state final execution rest

theorem invariant (I : List ParallelWorker → SharedState → Prop)
    (finish : ∀ state, I [] state → post state)
    (body : ∀ before worker after state, I (before ++ worker :: after) state →
      ∃ final, execute worker.todo worker.locals state = some final ∧ I (before ++ after) final) :
    ∀ pending state, I pending state → Ensures post pending none state := by
  intro pending
  induction n : pending.length using Nat.strongRecOn generalizing pending with
  | ind n ih =>
      intro state initial
      by_cases empty : pending = []
      · subst pending; exact .done (finish state initial)
      · apply Ensures.acquire empty
        intro before worker after split
        subst pending
        obtain ⟨final, execution, preserved⟩ := body before worker after state initial
        exact within worker.todo worker.locals state final execution
          (ih (before ++ after).length (by simp_all; omega) _ rfl final preserved)

theorem Ensures.mono (proof : Ensures post pending active state)
    (implication : ∀ state, post state → other state) : Ensures other pending active state := by
  induction proof with
  | done h => exact .done (implication _ h)
  | acquire nonempty _ ih => exact .acquire nonempty ih
  | step execution _ ih => exact .step execution ih
  | release empty _ ih => exact .release empty ih

/-- Validate the complete lock region, including the lock's identity and the
absence of assignments to its local name. No body operation is discarded. -/
def extract (worker : ParallelWorker) : Option (Nat × ParallelWorker) := do
  let .acquire (.name mutex) :: rest := worker.todo | none
  let .release (.name released) :: reversed := rest.reverse | none
  if mutex != released then none else do
    let .lock identity ← worker.locals.lookup mutex | none
    let body := reversed.reverse
    if body.any (fun
      | .acquire _ | .release _ | .branch .. | .loop .. => true
      | .read name _ | .assign name _ => name == mutex
      | _ => false) then none
    else some (identity, { worker with todo := body })

end Mutex

structure PyTrial where
  calls : List (Option ParallelWorker)
  initial : SharedState
  check : SharedState → Option Unit

namespace PyTrial

def readInts (heap : SharedState) (address : Nat) : Option (List Int) := do
  let .array values ← heap.objects[address]? | none
  values.mapM (fun | .int n => some n | _ => none)

def intItem (values : List Int) (index : Int) : Option Int :=
  Concurrent.readIntItem { objects := [.array (values.map .int)] } 0 index

def MutexReturns (trial : Option PyTrial) : Prop :=
  ∃ run, trial = some run ∧ ∃ mutex workers,
    run.initial.locked = [] ∧
    run.calls.mapM (fun call => do
      let (identity, worker) ← Mutex.extract (← call)
      if identity = mutex then some worker else none) = some workers ∧
    Mutex.Ensures (fun state => run.check state = some ()) workers none run.initial

/-- An actual worker exception or a failed post-execution assertion check.
Deadlock, unsupported execution and incomplete exploration are not exceptions. -/
def ObservedThrows (trial : Option PyTrial) : Prop :=
  ∃ run, trial = some run ∧
    ((∃ error, .error (.exception error) ∈ (parallelRun run.calls run.initial).outcomes) ∨
     ∃ final, ParallelRun.CanReturn (parallelRun run.calls run.initial) final ∧ run.check final = none)

/-- Two sound proof routes: the existing unbounded common-mutex certificate,
or total correctness of the general interleaving semantics. -/
def Returns (trial : Option PyTrial) : Prop :=
  MutexReturns trial ∨ ∃ run, trial = some run ∧
    (parallelRun run.calls run.initial).Eventually (fun
      | .ok state => run.check state = some ()
      | _ => False)

def Halts (trial : Option PyTrial) : Prop :=
  Returns trial ∨ ∃ run, trial = some run ∧ (parallelRun run.calls run.initial).Halts

def Throws (trial : Option PyTrial) : Prop :=
  ObservedThrows trial ∨ ∃ run initial final, trial = some run ∧
    (parallelRun run.calls run.initial).config = some initial ∧ initial.Reaches final ∧
    final.finished = true ∧
    ((∃ e, final.outcome = .error (.exception e)) ∨
      ∃ state, final.outcome = .ok state ∧ run.check state = none)

def CanDeadlock (trial : Option PyTrial) : Prop :=
  ∃ run, trial = some run ∧ (parallelRun run.calls run.initial).CanDeadlock

def CanDiverge (trial : Option PyTrial) : Prop :=
  ∃ run, trial = some run ∧ (parallelRun run.calls run.initial).CanDiverge

def DeadlockFree (trial : Option PyTrial) : Prop :=
  Halts trial ∨ ∃ run, trial = some run ∧ (parallelRun run.calls run.initial).DeadlockFree

/-- An executable input assertion followed, on success, by a concurrent trial.
The assertion is compiled from the helper, independently of the Lean theorem. -/
structure Call where
  condition : Option PyValue
  body : Option PyTrial

namespace Call

def Returns (call : Call) : Prop :=
  PyValue.IsTrue call.condition ∧ PyTrial.Returns call.body

def Throws (call : Call) : Prop :=
  call.condition = some (.bool false) ∨
    (PyValue.IsTrue call.condition ∧ PyTrial.Throws call.body)

def Halts (call : Call) : Prop :=
  call.condition = some (.bool false) ∨
    (PyValue.IsTrue call.condition ∧ PyTrial.Halts call.body)

def CanDeadlock (call : Call) : Prop :=
  PyValue.IsTrue call.condition ∧ PyTrial.CanDeadlock call.body

def CanDiverge (call : Call) : Prop :=
  PyValue.IsTrue call.condition ∧ PyTrial.CanDiverge call.body

def DeadlockFree (call : Call) : Prop :=
  call.condition = some (.bool false) ∨
    (PyValue.IsTrue call.condition ∧ PyTrial.DeadlockFree call.body)

theorem returns_halts {call : Call} (h : call.Returns) : call.Halts :=
  Or.inr ⟨h.1, Or.inl h.2⟩

theorem halts_deadlockFree {call : Call} (h : call.Halts) : call.DeadlockFree := by
  rcases h with failed | ⟨valid, halted⟩
  · exact Or.inl failed
  · exact Or.inr ⟨valid, Or.inl halted⟩

end Call

end PyTrial
end FormalSW.PyAst
