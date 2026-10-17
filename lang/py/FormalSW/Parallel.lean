import lang.py.FormalSW.Runtime

/-! Sequentially consistent interleaving of explicit calls over a shared heap.
Arguments and locals can hold scalars, object identities, and mutex identities.
Each heap access and lock operation is a scheduling step. The finite interpreter
rejects unimplemented source constructs rather than treating them as safe runs. -/
namespace FormalSW.PyAst

inductive SharedValue where
  | int (value : Int)
  | string (value : String)
  | bool (value : Bool)
  | none
  | ref (address : Nat)
  | lock (identity : Nat)
  deriving Repr, BEq, DecidableEq

def SharedValue.ofConstant : Constant → SharedValue
  | .int n => .int n | .string s => .string s | .bool b => .bool b | .none => .none

def SharedValue.toConstant : SharedValue → Option Constant
  | .int n => some (.int n) | .string s => some (.string s)
  | .bool b => some (.bool b) | .none => some .none | _ => Option.none

inductive SharedObject where
  | array (items : List SharedValue)
  | object (fields : List (String × SharedValue))
  deriving Repr, BEq, DecidableEq

structure SharedState where
  objects : List SharedObject := []
  locked : List Nat := []
  deriving Repr, BEq, DecidableEq

/-- Field and index lookup for specifications. References are stable heap indices. -/
def SharedState.field (state : SharedState) (address : Nat) (name : String) : Option SharedValue := do
  let .object fields ← state.objects[address]? | none
  fields.lookup name

def SharedState.item (state : SharedState) (address index : Nat) : Option SharedValue := do
  let .array values ← state.objects[address]? | none
  values[index]?

inductive SharedLocation where
  | field (object : Expr) (name : String)
  | item (object index : Expr)
  deriving Repr

inductive ParallelOp where
  | read (localName : String) (location : SharedLocation)
  | assign (localName : String) (value : Expr)
  | write (location : SharedLocation) (value : Expr)
  | acquire (mutex : Expr)
  | release (mutex : Expr)
  | yield
  | branch (test : Expr) (yes no : List ParallelOp)
  | loop (test : Expr) (body otherwise : List ParallelOp)
  deriving Repr

def sharedLocation : Expr → Option SharedLocation
  | .attribute object name => some (.field object name)
  | .subscript object index => some (.item object index)
  | _ => none

/-- Compile every statement without making a compound read/modify/write atomic. -/
def parallelOp : Stmt → Option ParallelOp
  | .assign [.name localName] value =>
      match sharedLocation value with
      | some location => some (.read localName location)
      | none => some (.assign localName value)
  | .assign [target] value => do return .write (← sharedLocation target) value
  | .expr (.call (.attribute mutex "acquire") []) => some (.acquire mutex)
  | .expr (.call (.attribute mutex "release") []) => some (.release mutex)
  | .expr (.call (.name "sleep") [.constant (.int 0)]) => some .yield
  | .expr (.constant .none) => some .yield
  | .ifThen test yes no => do return .branch test (← yes.mapM parallelOp) (← no.mapM parallelOp)
  | .whileDo test body otherwise => do return .loop test (← body.mapM parallelOp) (← otherwise.mapM parallelOp)
  | _ => none

private def importsPrimitive (module : Module) (source name : String) : Bool :=
  module.body.any fun
    | .importFrom origin names => origin == source && names.contains (name, name)
    | _ => false

abbrev SharedEnv := List (String × SharedValue)

structure ParallelWorker where
  todo : List ParallelOp
  locals : SharedEnv := []
  deriving Repr

mutual
  def ParallelOp.needs (primitive : String) : ParallelOp → Bool
    | .acquire _ | .release _ => primitive == "Lock"
    | .yield => primitive == "sleep"
    | .branch _ a b | .loop _ a b => needsList primitive a || needsList primitive b
    | _ => false
  def needsList (primitive : String) : List ParallelOp → Bool
    | [] => false
    | op :: rest => op.needs primitive || needsList primitive rest
end

mutual
  private def usesSleep : Stmt → Bool
    | .expr (.call (.name "sleep") _) => true
    | .ifThen _ a b | .whileDo _ a b => blockUsesSleep a || blockUsesSleep b
    | _ => false
  private def blockUsesSleep : List Stmt → Bool
    | [] => false
    | stmt :: rest => usesSleep stmt || blockUsesSleep rest
end

/-- Explicit arguments remove any required worker signature. The CLI checks the
supported source subset, plain data classes, annotations, and primitive bindings. -/
def parallelFunction (module : Module) (name : String) (values : List SharedValue) : Option ParallelWorker := do
  let (args, body) ← findFunctionIn module.body name
  if args.length != values.length then none
  else
    let body := executableBody body
    let program ← body.mapM parallelOp
    if program.any (ParallelOp.needs "Lock") &&
        !importsPrimitive module "threading" "Lock" then none
    else if body.any usesSleep &&
        !importsPrimitive module "time" "sleep" then none
    else some ⟨program, (args.map Arg.name).zip values⟩

inductive ParallelFailure where
  | deadlock
  | releaseUnlocked
  | exception (value : ExceptionObject)
  | unsupported
  | incomplete
  | invalidSchedule
  | invalidReference
  deriving Repr, DecidableEq

abbrev SharedResult := Except ParallelFailure
abbrev ParallelOutcome := SharedResult SharedState

private def pythonError (name : String) : ParallelFailure := .exception ⟨name, []⟩

/-- Pure local expressions have no shared-memory accesses. Reads are separate ops. -/
def sharedExpr (env : SharedEnv) : Expr → SharedResult SharedValue
  | .constant value => .ok (.ofConstant value)
  | .name name => match env.lookup name with
      | some value => .ok value | none => .error (pythonError "UnboundLocalError")
  | .binOp left op right => do
      let left ← sharedExpr env left
      let right ← sharedExpr env right
      match left.toConstant, right.toConstant with
      | some left, some right => match scalarBinary op left right with
          | some (.ok value) => .ok (.ofConstant value)
          | some (.error error) => .error (.exception error)
          | none => .error .unsupported
      | _, _ => .error .unsupported
  | .unaryOp .uSub operand => do
      let .int n ← sharedExpr env operand | .error .unsupported
      return .int (-n)
  | .unaryOp .not operand => do
      let value ← sharedExpr env operand
      let some scalar := value.toConstant | .error .unsupported
      return .bool (!scalarTruth scalar)
  | .compare left [(op, right)] => do
      let left ← sharedExpr env left
      let right ← sharedExpr env right
      let some left := left.toConstant | .error .unsupported
      let some right := right.toConstant | .error .unsupported
      let some result := scalarCompare op left right | .error (pythonError "TypeError")
      return .bool result
  | _ => .error .unsupported

private def objectAt (state : SharedState) (value : SharedValue) : SharedResult (Nat × SharedObject) :=
  match value with
  | .ref address => match state.objects[address]? with
      | some object => .ok (address, object)
      | none => .error .invalidReference
  | _ => .error (pythonError "TypeError")

private def arrayIndex (size : Nat) (value : SharedValue) : SharedResult Nat := do
  let .int index := value | .error (pythonError "TypeError")
  let index := if index < 0 then (size : Int) + index else index
  if index < 0 || index ≥ size then .error (pythonError "IndexError") else .ok index.toNat

private def resolveLocation (state : SharedState) (env : SharedEnv) : SharedLocation →
    SharedResult (Nat × SharedObject × Sum String Nat)
  | .field object name => do
      let value ← sharedExpr env object
      let .ref _ := value | .error (pythonError "AttributeError")
      let (address, object) ← objectAt state value
      match object with
      | .object _ => return (address, object, .inl name)
      | _ => .error (pythonError "AttributeError")
  | .item object index => do
      let (address, object) ← objectAt state (← sharedExpr env object)
      match object with
      | .array values => return (address, object, .inr (← arrayIndex values.length (← sharedExpr env index)))
      | _ => .error (pythonError "TypeError")

def sharedRead (state : SharedState) (env : SharedEnv) (location : SharedLocation) : SharedResult SharedValue := do
  let (_, object, key) ← resolveLocation state env location
  match object, key with
  | .object fields, .inl name => match fields.lookup name with
      | some value => .ok value | none => .error (pythonError "AttributeError")
  | .array values, .inr index => match values[index]? with
      | some value => .ok value | none => .error (pythonError "IndexError")
  | _, _ => .error .unsupported

def sharedWrite (state : SharedState) (env : SharedEnv) (location : SharedLocation)
    (value : SharedValue) : SharedResult SharedState := do
  let (address, object, key) ← resolveLocation state env location
  let object ← match object, key with
    | .object fields, .inl name =>
        .ok (.object (if fields.any (fun entry => entry.1 == name) then
          fields.map (fun entry => if entry.1 == name then (name, value) else entry)
          else fields ++ [(name, value)]))
    | .array values, .inr index => .ok (.array (values.set index value))
    | _, _ => .error .unsupported
  return { state with objects := state.objects.set address object }

structure ParallelState where
  shared : SharedState
  workers : List ParallelWorker
  deriving Repr

/-- A blocked acquire has no transition. Locks have independent identities, so
sharing the data but using different mutexes gives no mutual exclusion. -/
def parallelStep (state : SharedState) (worker : ParallelWorker) :
    Option (SharedResult (SharedState × ParallelWorker)) := do
  let op :: rest := worker.todo | none
  let next := { worker with todo := rest }
  match op with
  | .acquire mutex =>
      match sharedExpr worker.locals mutex with
      | .error error => some (.error error)
      | .ok (.lock id) =>
          if state.locked.contains id then none
          else some (.ok ({ state with locked := id :: state.locked }, next))
      | _ => some (.error (pythonError "AttributeError"))
  | .release mutex => some do
      let .lock id ← sharedExpr worker.locals mutex | .error (pythonError "AttributeError")
      if state.locked.contains id then
        return ({ state with locked := state.locked.filter (· != id) }, next)
      else .error (pythonError "RuntimeError")
  | .read name location => some do
      let value ← sharedRead state worker.locals location
      return (state, { next with locals := (name, value) :: worker.locals })
  | .assign name expression => some do
      let value ← sharedExpr worker.locals expression
      return (state, { next with locals := (name, value) :: worker.locals })
  | .write location expression => some do
      let value ← sharedExpr worker.locals expression
      let state ← sharedWrite state worker.locals location value
      return (state, next)
  | .yield => some (.ok (state, next))
  | .branch test yes no => some do
      let value ← sharedExpr worker.locals test
      let some value := value.toConstant | .error .unsupported
      return (state, { next with todo := (if scalarTruth value then yes else no) ++ rest })
  | .loop test body otherwise => some do
      let value ← sharedExpr worker.locals test
      let some value := value.toConstant | .error .unsupported
      return (state, { next with todo := if scalarTruth value then
        body ++ [.loop test body otherwise] ++ rest else otherwise ++ rest })

/-- A joined batch retains worker failures while remaining workers finish.
An exception in one worker cannot conceal another worker's deadlock or loop. -/
structure ParallelConfig where
  state : ParallelState
  failures : List ParallelFailure := []
  deriving Repr

def ParallelConfig.finished (config : ParallelConfig) : Bool :=
  config.state.workers.all (fun w => w.todo.isEmpty)

/-- Coverage/model failures cannot be concealed by an earlier Python exception. -/
def ParallelConfig.outcome (config : ParallelConfig) : ParallelOutcome :=
  match config.failures.find? (fun | .exception _ => false | _ => true) with
  | some error => .error error
  | none => match config.failures with
    | [] => .ok config.state.shared
    | error :: _ => .error error

/-- Selecting a blocked or completed worker is not an execution step. -/
def parallelChoose (config : ParallelConfig) (index : Nat) : Option ParallelConfig := do
  let worker ← config.state.workers[index]?
  let result ← parallelStep config.state.shared worker
  match result with
  | .ok (shared, next) => return { config with state :=
      ⟨shared, config.state.workers.set index next⟩ }
  | .error error => return {
      state := ⟨config.state.shared, config.state.workers.set index { worker with todo := [] }⟩
      failures := config.failures ++ [error] }

def ParallelConfig.next (config : ParallelConfig) : List ParallelConfig :=
  (List.range config.state.workers.length).filterMap (parallelChoose config)

/-- Fuel bounds observation only. Incomplete exploration is never divergence. -/
def exploreParallel : Nat → ParallelConfig → List ParallelOutcome
  | fuel, config =>
      if config.finished then [config.outcome]
      else match fuel with
        | 0 => [.error .incomplete]
        | fuel + 1 =>
            let following := config.next
            if following.isEmpty then [.error .deadlock]
            else following.flatMap (exploreParallel fuel)

def parallelExplore (fuel : Nat) (state : ParallelState) : List ParallelOutcome :=
  exploreParallel fuel ⟨state, []⟩

/-- Keep the program, not just a bounded list of observed outcomes. -/
structure ParallelRun where
  calls : List (Option ParallelWorker)
  initial : SharedState
  deriving Repr

def parallelRun (calls : List (Option ParallelWorker)) (initial : SharedState) : ParallelRun :=
  ⟨calls, initial⟩

def ParallelRun.config (run : ParallelRun) : Option ParallelConfig := do
  return ⟨⟨run.initial, ← run.calls.mapM id⟩, []⟩

def ParallelRun.outcomes (run : ParallelRun) : List ParallelOutcome :=
  match run.config with
  | none => [.error .unsupported]
  | some config => exploreParallel ((config.state.workers.map (fun w => w.todo.length)).sum) config

def ParallelRun.Ensures (run : ParallelRun) (post : SharedState → Prop) : Prop :=
  run.outcomes ≠ [] ∧ ∀ outcome ∈ run.outcomes, match outcome with
    | .ok value => post value
    | .error _ => False

instance (run : ParallelRun) (post : SharedState → Prop) [DecidablePred post] : Decidable (run.Ensures post) :=
  letI : DecidablePred (fun outcome : ParallelOutcome => match outcome with
      | .ok value => post value | .error _ => False) := fun outcome => match outcome with
        | .ok _ => inferInstance | .error _ => inferInstance
  inferInstanceAs (Decidable (run.outcomes ≠ [] ∧ ∀ outcome ∈ run.outcomes, match outcome with
      | .ok value => post value | .error _ => False))

def ParallelRun.CanReturn (run : ParallelRun) (value : SharedState) : Prop := .ok value ∈ run.outcomes
instance (run : ParallelRun) (value : SharedState) : Decidable (run.CanReturn value) :=
  inferInstanceAs (Decidable (.ok value ∈ run.outcomes))

theorem ParallelRun.Ensures.of_canReturn {run : ParallelRun} {post : SharedState → Prop}
    (guarantee : run.Ensures post) {value : SharedState} (reachable : run.CanReturn value) : post value :=
  guarantee.2 (.ok value) reachable

def replayParallel (config : ParallelConfig) : List Nat → ParallelOutcome
  | [] => if config.finished then config.outcome else .error .incomplete
  | index :: rest => match parallelChoose config index with
      | none => .error .invalidSchedule
      | some next => replayParallel next rest

def parallelReplay (state : ParallelState) (schedule : List Nat) : ParallelOutcome :=
  replayParallel ⟨state, []⟩ schedule

macro "Parallel(" calls:term "," initial:term ")" : term => `(parallelRun $calls $initial)
macro "Ensures(" run:term "," post:term ")" : term => `(ParallelRun.Ensures $run $post)
macro "CanReturn(" run:term "," value:term ")" : term => `(ParallelRun.CanReturn $run $value)

end FormalSW.PyAst
