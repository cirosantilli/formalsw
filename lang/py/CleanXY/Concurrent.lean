import lang.py.CleanXY.Parallel

/-! Unbounded reference-object programs protected by one common mutex.
`LockedEnsures` exposes acquire, every individual body operation, and release.
While a worker owns the mutex, all other workers are blocked at acquire.
Its inductive proof requires termination and covers every choice of next owner. -/
namespace CleanXY.PyAst
/-- Follow a reference path. A missing field or dereferencing None fails, so a
scenario assertion cannot pass merely because its expression raised. -/
def SharedState.readPath (state : SharedState) : SharedValue → List String → Option SharedValue
  | value, [] => some value
  | .ref address, field :: rest => do
      let value ← state.field address field
      state.readPath value rest
  | _, _ :: _ => none

namespace Concurrent

abbrev Heap := Nat → String → Option Nat
abbrev Env := List (String × Option Nat)

inductive Op where
  | read (localName object field : String)
  | write (object field value : String)
  | yield
  deriving Repr, DecidableEq

def compileOp : Stmt → Option Op
  | .assign [.name localName] (.attribute (.name object) field) => some (.read localName object field)
  | .assign [.attribute (.name object) field] (.name value) => some (.write object field value)
  | .expr (.call (.name "sleep") [.constant (.int 0)]) => some .yield
  | .expr (.constant .none) => some .yield
  | _ => none

def put (heap : Heap) (object : Nat) (field : String) (value : Option Nat) : Heap :=
  fun address name => if address = object ∧ name = field then value else heap address name

def step : Op → Heap → Env → Option (Heap × Env)
  | .read localName object field, heap, env => do
      let some address ← env.lookup object | none
      return (heap, (localName, heap address field) :: env)
  | .write object field value, heap, env => do
      let some address ← env.lookup object | none
      let value ← env.lookup value
      return (put heap address field value, env)
  | .yield, heap, env => some (heap, env)

def execute : List Op → Heap → Env → Option Heap
  | [], heap, _ => some heap
  | op :: rest, heap, env => do
      let (heap, env) ← step op heap env
      execute rest heap env

/-- A successful proof covers every scheduling choice and rules out faults and
infinite executions. Body operations are separate transitions, not atomic. -/
inductive LockedEnsures {Job : Type} (program : Job → List Op × Env)
    (post : Heap → Prop) : List Job → Option (List Op × Env) → Heap → Prop where
  | done : post heap → LockedEnsures program post [] none heap
  | acquire : pending ≠ [] →
      (∀ before job after, pending = before ++ job :: after →
        LockedEnsures program post (before ++ after) (some (program job)) heap) →
      LockedEnsures program post pending none heap
  | step : step op heap env = some (nextHeap, nextEnv) →
      LockedEnsures program post pending (some (rest, nextEnv)) nextHeap →
      LockedEnsures program post pending (some (op :: rest, env)) heap
  | release : LockedEnsures program post pending none heap →
      LockedEnsures program post pending (some ([], env)) heap

theorem within {Job : Type} {program : Job → List Op × Env} {post : Heap → Prop}
    {ops : List Op} {heap final : Heap} {env : Env} {pending : List Job}
    (execution : execute ops heap env = some final)
    (continuation : LockedEnsures program post pending none final) :
    LockedEnsures program post pending (some (ops, env)) heap := by
  induction ops generalizing heap env with
  | nil => simp [execute] at execution; subst final; exact .release continuation
  | cons op rest ih =>
      simp only [execute] at execution
      cases h : step op heap env with
      | none => simp [h] at execution
      | some pair =>
          rcases pair with ⟨nextHeap, nextEnv⟩
          simp only [h] at execution
          exact .step h (ih execution)

/-- The reusable mutex rule: verify one critical section for arbitrary remaining
jobs and heap. Induction proves all finite batch sizes and all owner orders. -/
theorem invariant {Job : Type} (program : Job → List Op × Env)
    (I : List Job → Heap → Prop) (post : Heap → Prop)
    (finish : ∀ heap, I [] heap → post heap)
    (body : ∀ before job after heap, I (before ++ job :: after) heap →
      ∃ final, execute (program job).1 heap (program job).2 = some final ∧
        I (before ++ after) final) :
    ∀ pending heap, I pending heap → LockedEnsures program post pending none heap := by
  intro pending
  induction n : pending.length using Nat.strongRecOn generalizing pending with
  | ind n ih =>
      intro heap initial
      by_cases empty : pending = []
      · subst pending; exact .done (finish heap initial)
      · apply LockedEnsures.acquire empty
        intro before job after split
        subst pending
        obtain ⟨final, execution, preserved⟩ := body before job after heap initial
        apply within execution
        exact ih (before ++ after).length (by simp_all; omega) (before ++ after) rfl final preserved

/-- Sequential assertions and field reads used by ordinary Python trial helpers. -/
def read (heap : Heap) (object : Option Nat) (field : String) : Option (Option Nat) :=
  object.map (fun address => heap address field)

def check (condition : Bool) : Option Unit := if condition then some () else none

def readConcrete (heap : SharedState) (object : Option Nat) (field : String) : Option (Option Nat) := do
  let address ← object
  match ← heap.field address field with
  | .ref value => some (some value)
  | .none => some none
  | _ => none

/-- Ordinary integer-list indexing, including Python's negative indices.
Out-of-bounds access fails the trial instead of inventing a value. -/
def readIntItem (heap : SharedState) (object : Nat) (index : Int) : Option Int :=
  match sharedRead heap [("object", .ref object)]
      (.item (.name "object") (.constant (.int index))) with
  | .ok (.int value) => some value
  | _ => none

/-- Setup targets are statically restricted to freshly allocated object identities
and declared fields. The finite representation is used to check counterexamples. -/
def putConcrete (heap : SharedState) (object : Nat) (field : String) (value : Option Nat) : SharedState :=
  { heap with objects := heap.objects.modify object (fun
      | .object fields => .object (fields.map fun (name, old) =>
          (name, if name = field then value.map SharedValue.ref |>.getD .none else old))
      | other => other) }

theorem LockedEnsures.mono {Job : Type} {program : Job → List Op × Env}
    {post other : Heap → Prop} {pending active heap}
    (implication : ∀ state, post state → other state)
    (proof : LockedEnsures program post pending active heap) :
    LockedEnsures program other pending active heap := by
  induction proof with
  | done h => exact .done (implication _ h)
  | acquire nonempty _ ih => exact .acquire nonempty ih
  | step execution _ ih => exact .step execution ih
  | release _ ih => exact .release ih

/-- Extract a complete acquire/body/release region from the actual Python AST.
Only reference-field accesses and yields are accepted inside the region. -/
def protectedBody (module : Module) (name : String) : Option (List String × String × List Op) := do
  let (args, statements) ← findFunctionIn module.body name
  let .expr (.call (.attribute (.name mutex) "acquire") []) :: body := executableBody statements | none
  let .expr (.call (.attribute (.name released) "release") []) :: reversed := body.reverse | none
  if mutex != released || !(args.map Arg.name).contains mutex then none
  else return ((args.map Arg.name).filter (· != mutex), mutex, ← reversed.reverse.mapM compileOp)

def Ensures {Job : Type} (module : Module) (function : String)
    (parameters : List String) (mutex : String) (arguments : Job → List (Option Nat))
    (jobs : List Job) (heap : Heap) (post : Heap → Prop) : Prop :=
  ∃ ops, protectedBody module function = some (parameters, mutex, ops) ∧
    LockedEnsures (fun job => (ops, parameters.zip (arguments job))) post jobs none heap

end Concurrent
end CleanXY.PyAst
