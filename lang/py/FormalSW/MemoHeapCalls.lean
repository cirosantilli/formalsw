import lang.py.FormalSW.HeapCalls
import lang.py.FormalSW.MemoCalls

/-! Heap callers with pure scalar memoized helpers. Every cached helper executes
in the scalar memoizing machine; its cache survives subsequent heap calls. -/
namespace FormalSW.PyAst.MemoHeapCalls
abbrev Value := Mutable.Value
abbrev Heap := Mutable.Heap
abbrev Env := Mutable.Env
abbrev Completion := Mutable.Completion
open MemoCalls (Cache Specification)

inductive State where
  | heap (current : HeapCalls.State) (cache : Cache)
  | scalar (current : MemoCalls.State) (stack : List HeapCalls.Frame) (heap : Heap)

def scalarArguments : List Value → Option (List Constant)
  | [] => some []
  | .scalar value :: rest => (value :: ·) <$> scalarArguments rest
  | _ => none

@[simp] theorem scalarArguments_map (values : List Constant) :
    scalarArguments (values.map Mutable.Value.scalar) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [scalarArguments, ih]

private def advance (cache : Cache) : Step HeapCalls.State Completion → Step State Completion
  | .next current => .next (.heap current cache)
  | .done outcome => .done outcome
  | .unsupported => .unsupported

def step (module : Module) (anchors : Nat) (state : State)
    (globals : Mutable.Globals := []) : Step State Completion :=
  match state with
  | .heap current cache =>
      match current.work with
      | .operation (.call name) values =>
          if name ∈ module.memoizedFunctions then
            match scalarArguments values with
            | none => .unsupported
            | some arguments => .next (.scalar ⟨⟨.invoke name arguments, []⟩, [], cache⟩ current.stack current.heap)
          else advance cache (HeapCalls.step (globals := globals) module anchors current)
      | _ => advance cache (HeapCalls.step (globals := globals) module anchors current)
  | .scalar current stack heap =>
      match MemoCalls.step module module.memoizedFunctions current with
      | .next next => .next (.scalar next stack heap)
      | .unsupported => .unsupported
      | .done (.ok value) => .next (.heap ⟨.value (.scalar value), stack, heap⟩ current.cache)
      | .done (.error error) => .done (.ok ⟨.error
          (Calls.generatorException (stack.any HeapCalls.Frame.inGenerator) error), globals, heap, anchors⟩)

def call (module : Module) (name : String) (values : List Value) (heap : Heap)
    (globals : Mutable.Globals := []) : Mutable.Call :=
  ⟨⟨State, .heap ⟨.operation (.call name) values, [], heap⟩ Cache.empty,
    step (globals := globals) module heap.length⟩⟩

def evaluate (module : Module) (env : Env) (expression : Expr) (heap : Heap)
    (globals : Mutable.Globals := []) : Mutable.Call :=
  ⟨⟨State, .heap ⟨.expr expression env, [], heap⟩ Cache.empty,
    step (globals := globals) module heap.length⟩⟩

def Condition (module : Module) (env : Env) (expression : Expr) (heap : Heap)
    (globals : Mutable.Globals := []) : Prop :=
  ∃ finalHeap, (evaluate (globals := globals) module env expression heap).Finishes
    ⟨.ok (.scalar (.bool true)), globals, finalHeap, heap.length⟩

def scalarStep (module : Module) (state : State) : Step State Constant :=
  match step module 0 state with
  | .next next => .next next
  | .unsupported => .unsupported
  | .done (.ok completion) => match completion.outcome with
      | .ok (.scalar value) => .done (.ok value)
      | .ok (.ref _) => .unsupported
      | .error error => .done (.error error)
  | .done (.error _) => .unsupported

def scalarFunction (module : Module) (name : String) (values : List Constant) : Execution Constant :=
  ⟨State, .heap ⟨.operation (.call name) (values.map Mutable.Value.scalar), [], []⟩ Cache.empty, scalarStep module⟩

variable {globals : Mutable.Globals}

inductive Reaches (module : Module) (anchors : Nat) : State → State → (globals : Mutable.Globals := []) → Prop where
  | refl {globals : Mutable.Globals} : Reaches (globals := globals) module anchors state state
  | next {globals : Mutable.Globals} : step (globals := globals) module anchors state = .next following →
      Reaches (globals := globals) module anchors following final → Reaches (globals := globals) module anchors state final

theorem Reaches.trans (run : Reaches (globals := globals) module anchors a b)
    (rest : Reaches (globals := globals) module anchors b c) : Reaches (globals := globals) module anchors a c := by
  induction run with
  | refl => exact rest
  | next transition _ ih => exact .next transition (ih rest)

theorem Reaches.finishes (run : Reaches (globals := globals) module anchors a b)
    (rest : Finishes (step (globals := globals) module anchors) b outcome) :
    Finishes (step (globals := globals) module anchors) a outcome := by
  induction run with
  | refl => exact rest
  | next transition _ ih => exact .next transition (ih rest)

def transparent (module : Module) (state : HeapCalls.State) : Prop :=
  match state.work with
  | .operation (.call name) _ => name ∉ module.memoizedFunctions
  | _ => True

theorem step_raw (plain : transparent module current)
    (transition : HeapCalls.step (globals := globals) module anchors current = .next following) :
    step (globals := globals) module anchors (.heap current cache) = .next (.heap following cache) := by
  rcases current with ⟨work, stack, heap⟩
  cases work <;> try { simp only [step]; rw [transition]; rfl }
  case operation operation values =>
    cases operation <;> try { simp only [step]; rw [transition]; rfl }
    case call name =>
      simp only [transparent] at plain
      simp only [step, if_neg plain]
      rw [transition]
      rfl

def Runs (module : Module) (spec : Specification) (anchors : Nat)
    (initial final : HeapCalls.State) (globals : Mutable.Globals := []) : Prop :=
  ∀ cache, cache.Valid spec → ∃ updated, updated.Valid spec ∧
    Reaches (globals := globals) module anchors (.heap initial cache) (.heap final updated)

namespace Runs

theorem refl : Runs (globals := globals) module spec anchors state state :=
  fun cache valid => ⟨cache, valid, .refl⟩

theorem trans (run : Runs (globals := globals) module spec anchors a b)
    (rest : Runs (globals := globals) module spec anchors b c) :
    Runs (globals := globals) module spec anchors a c := by
  intro cache valid
  obtain ⟨middle, valid, run⟩ := run cache valid
  obtain ⟨final, valid, rest⟩ := rest middle valid
  exact ⟨final, valid, run.trans rest⟩

theorem raw (plain : transparent module current)
    (transition : HeapCalls.step (globals := globals) module anchors current = .next following) :
    Runs (globals := globals) module spec anchors current following :=
  fun cache valid => ⟨cache, valid, .next (step_raw plain transition) .refl⟩

theorem next (plain : transparent module current)
    (transition : HeapCalls.step (globals := globals) module anchors current = .next following)
    (rest : Runs (globals := globals) module spec anchors following final) :
    Runs (globals := globals) module spec anchors current final := (raw plain transition).trans rest

end Runs

def Evaluates (module : Module) (spec : Specification) (env : Env) (expression : Expr)
    (heap : Heap) (value : Value) (finalHeap : Heap) (globals : Mutable.Globals := []) : Prop :=
  ∀ anchors stack, Runs (globals := globals) module spec anchors
    ⟨.expr expression env, stack, heap⟩ ⟨.value value, stack, finalHeap⟩

def ReturnsValue (module : Module) (spec : Specification) (name : String) (values : List Value)
    (heap : Heap) (value : Value) (finalHeap : Heap) (globals : Mutable.Globals := []) : Prop :=
  ∀ anchors stack, Runs (globals := globals) module spec anchors
    ⟨.operation (.call name) values, stack, heap⟩ ⟨.value value, stack, finalHeap⟩

def BlockReturns (module : Module) (spec : Specification) (env : Env) (body : List Stmt)
    (heap : Heap) (value : Value) (finalHeap : Heap) (globals : Mutable.Globals := []) : Prop :=
  ∀ anchors stack, Runs (globals := globals) module spec anchors
    ⟨.block body env, stack, heap⟩ ⟨.value value, stack, finalHeap⟩

theorem Evaluates.finishes (run : Evaluates (globals := globals) module spec env expression heap value finalHeap) :
    (evaluate (globals := globals) module env expression heap).Finishes ⟨.ok value, globals, finalHeap, heap.length⟩ := by
  obtain ⟨cache, _, reached⟩ := run heap.length [] Cache.empty (Cache.valid_empty spec)
  exact reached.finishes (.done rfl)

theorem Evaluates.condition_iff (run : Evaluates (globals := globals) module spec env expression heap value finalHeap) :
    Condition (globals := globals) module env expression heap ↔ value = .scalar (.bool true) := by
  constructor
  · rintro ⟨otherHeap, finished⟩
    have same := run.finishes.unique finished
    cases same
    rfl
  · intro same
    subst value
    exact ⟨finalHeap, run.finishes⟩

theorem ReturnsValue.finishes (run : ReturnsValue (globals := globals) module spec name values heap value finalHeap) :
    (call (globals := globals) module name values heap).Finishes ⟨.ok value, globals, finalHeap, heap.length⟩ := by
  obtain ⟨cache, _, reached⟩ := run heap.length [] Cache.empty (Cache.valid_empty spec)
  exact reached.finishes (.done rfl)

theorem ReturnsValue.returns (run : ReturnsValue (globals := globals) module spec name values heap value finalHeap) :
    (call (globals := globals) module name values heap).Returns := ⟨value, globals, finalHeap, heap.length, run.finishes⟩

theorem Reaches.scalar_finishes (run : Reaches module 0 a b)
    (rest : Finishes (scalarStep module) b outcome) : Finishes (scalarStep module) a outcome := by
  generalize empty : ([] : Mutable.Globals) = context at run
  induction run with
  | refl => exact rest
  | next transition _ ih =>
      cases empty
      exact .next (by simp [scalarStep, transition]) (ih rest rfl)

theorem ReturnsValue.scalar_finishes
    (run : ReturnsValue module spec name (values.map Mutable.Value.scalar) [] (.scalar value) heap) :
    Finishes (scalarFunction module name values).step (scalarFunction module name values).initial (.ok value) := by
  obtain ⟨cache, _, reached⟩ := run 0 [] Cache.empty (Cache.valid_empty spec)
  exact reached.scalar_finishes (.done rfl)

theorem ReturnsValue.scalar_returns
    (run : ReturnsValue module spec name (values.map Mutable.Value.scalar) [] (.scalar value) heap) :
    (scalarFunction module name values).Returns := ⟨value, ReturnsValue.scalar_finishes run⟩

theorem Reaches.scalar (run : MemoCalls.Reaches module module.memoizedFunctions a b) :
    Reaches (globals := globals) module anchors (.scalar a stack heap) (.scalar b stack heap) := by
  induction run with
  | refl => exact .refl
  | next transition _ ih => exact .next (by simp [step, transition]) ih

theorem ReturnsValue.memoized (cached : name ∈ module.memoizedFunctions)
    (run : MemoCalls.ReturnsValue module module.memoizedFunctions spec name values value) :
    ReturnsValue (globals := globals) module spec name (values.map Mutable.Value.scalar) heap (.scalar value) heap := by
  intro anchors stack cache valid
  obtain ⟨updated, valid, reached⟩ := run [] [] cache valid
  refine ⟨updated, valid, .next ?_ ((Reaches.scalar reached).trans (.next rfl .refl))⟩
  simp [step, cached]

/-- A source module has no way to enter the target's cached helpers. -/
def CacheDisjoint (target source : Module) : Prop :=
  ∀ name, name ∈ target.memoizedFunctions → findFunctionIn source.body name = none ∧
    libraryFunction source name = none ∧ source.findClass name = none

theorem Runs.from_heap (extension : HeapCalls.Extends target source)
    (disjoint : CacheDisjoint target source)
    (run : HeapCalls.Reaches (globals := globals) source anchors initial final) :
    Runs (globals := globals) target spec anchors initial final := by
  induction run with
  | refl => exact .refl
  | @next current following final globals transition rest ih =>
      apply Runs.next (following := following) ?_ ?_ ih
      · rcases current with ⟨work, stack, heap⟩
        cases work <;> try trivial
        case operation operation values =>
          cases operation <;> try trivial
          case call name =>
            intro cached
            obtain ⟨absent, library, classless⟩ := disjoint name cached
            simp [HeapCalls.step, absent, library, HeapCalls.construct, classless] at transition
      · rw [HeapCalls.step_extend extension _ (by simp [transition])]
        exact transition

theorem ReturnsValue.from_heap (extension : HeapCalls.Extends target source)
    (disjoint : CacheDisjoint target source)
    (run : HeapCalls.ReturnsValue (globals := globals) source name values heap value finalHeap) :
    ReturnsValue (globals := globals) target spec name values heap value finalHeap :=
  fun anchors stack => Runs.from_heap extension disjoint (run anchors stack)

theorem Evaluates.from_heap (extension : HeapCalls.Extends target source)
    (disjoint : CacheDisjoint target source)
    (run : HeapCalls.Evaluates (globals := globals) source env expression heap value finalHeap) :
    Evaluates (globals := globals) target spec env expression heap value finalHeap :=
  fun anchors stack => Runs.from_heap extension disjoint (run anchors stack)

namespace Evaluates

 theorem constant : Evaluates (globals := globals) module spec env (.constant value) heap (.scalar value) heap :=
  fun _ _ => Runs.next trivial rfl .refl

theorem lookup (found : env name = some value) :
    Evaluates (globals := globals) module spec env (.name name) heap value heap :=
  fun _ _ => Runs.next trivial (by simp [HeapCalls.step, found]) .refl

theorem binary (left : Evaluates (globals := globals) module spec env a heap av middle)
    (right : Evaluates (globals := globals) module spec env b middle bv afterRight)
    (operation : Mutable.binary op av bv afterRight = some (.ok value, finalHeap)) :
    Evaluates (globals := globals) module spec env (.binOp a op b) heap value finalHeap := by
  intro anchors stack
  exact Runs.next trivial rfl ((left _ _).trans (Runs.next trivial rfl ((right _ _).trans
    (Runs.next trivial (by simp [HeapCalls.step, HeapCalls.result, HeapCalls.run, operation]) .refl))))

theorem compare (left : Evaluates (globals := globals) module spec env a heap av middle)
    (right : Evaluates (globals := globals) module spec env b middle bv afterRight)
    (operation : HeapCalls.compare op av bv afterRight = some (.ok value, finalHeap)) :
    Evaluates (globals := globals) module spec env (.compare a [(op, b)]) heap value finalHeap := by
  intro anchors stack
  exact Runs.next trivial rfl ((left _ _).trans (Runs.next trivial rfl ((right _ _).trans
    (Runs.next trivial (by simp [HeapCalls.step, HeapCalls.result, HeapCalls.run, operation]) .refl))))

inductive Arguments (module : Module) (spec : Specification) (env : Env) :
    List Expr → Heap → List Value → Heap → (globals : Mutable.Globals := []) → Prop where
  | nil {globals : Mutable.Globals} : Arguments (globals := globals) module spec env [] heap [] heap
  | cons {globals : Mutable.Globals} : Evaluates (globals := globals) module spec env expression heap value middle →
      Arguments (globals := globals) module spec env expressions middle values finalHeap →
      Arguments (globals := globals) module spec env (expression :: expressions) heap (value :: values) finalHeap

theorem arguments_reach (run : Arguments (globals := globals) module spec env expressions heap values finalHeap)
    (operation : HeapCalls.Operation) (done : List Value) (anchors : Nat) (stack : List HeapCalls.Frame) :
    Runs (globals := globals) module spec anchors (HeapCalls.argumentsState operation env done expressions stack heap)
      ⟨.operation operation (done ++ values), stack, finalHeap⟩ := by
  induction run generalizing done with
  | nil => simp [HeapCalls.argumentsState]; exact .refl
  | @cons expression heap value middle expressions values finalHeap globals head tail ih =>
      apply (head _ _).trans
      refine Runs.next trivial rfl ?_
      simpa [List.append_assoc] using ih (done ++ [value])

theorem call (arguments : Arguments (globals := globals) module spec env expressions heap values middle)
    (callee : ReturnsValue (globals := globals) module spec name values middle value finalHeap) :
    Evaluates (globals := globals) module spec env (.call (.name name) expressions) heap value finalHeap := by
  intro anchors stack
  exact Runs.next trivial rfl ((arguments_reach arguments (.call name) [] anchors stack).trans (callee anchors stack))

theorem builtin (arguments : Arguments (globals := globals) module spec env expressions heap values middle)
    (operation : HeapCalls.primitive (.builtin name) values middle = some (.ok value, finalHeap)) :
    Evaluates (globals := globals) module spec env (.builtinCall name expressions) heap value finalHeap := by
  intro anchors stack
  exact Runs.next trivial rfl ((arguments_reach arguments (.builtin name) [] anchors stack).trans
    (Runs.next trivial (by simp [HeapCalls.step, HeapCalls.result, HeapCalls.run, operation]) .refl))

end Evaluates

namespace BlockReturns

theorem return_value (evaluated : Evaluates (globals := globals) module spec env expression heap value finalHeap) :
    BlockReturns (globals := globals) module spec env (.return expression :: rest) heap value finalHeap :=
  fun anchors stack => Runs.next trivial rfl (evaluated anchors stack)

theorem assign (evaluated : Evaluates (globals := globals) module spec env expression heap value middle)
    (rest : BlockReturns (globals := globals) module spec (HeapCalls.setLocal env name value) body middle answer finalHeap) :
    BlockReturns (globals := globals) module spec env (.assign [.name name] expression :: body) heap answer finalHeap :=
  fun anchors stack => Runs.next trivial rfl ((evaluated anchors _).trans (Runs.next trivial rfl (rest anchors stack)))

theorem augAssign (lookup : env name = some left)
    (evaluated : Evaluates (globals := globals) module spec env expression heap right middle)
    (operation : HeapCalls.inplace op left right middle = some (.ok value, afterOperation))
    (rest : BlockReturns (globals := globals) module spec (HeapCalls.setLocal env name value) body afterOperation answer finalHeap) :
    BlockReturns (globals := globals) module spec env (.augAssign (.name name) op expression :: body) heap answer finalHeap := by
  intro anchors stack
  apply Runs.trans (Runs.raw (current := ⟨.block (.augAssign (.name name) op expression :: body) env, stack, heap⟩) trivial rfl)
  apply (Evaluates.lookup (globals := globals) (module := module) (spec := spec) (heap := heap) lookup anchors _).trans
  apply Runs.trans (Runs.raw (current := ⟨.value left, .binaryLeft op expression env true :: .assign name body env :: stack, heap⟩) trivial rfl)
  apply (evaluated anchors _).trans
  exact Runs.next (following := ⟨.value value, .assign name body env :: stack, afterOperation⟩) trivial
    (by simp [HeapCalls.step, HeapCalls.result, HeapCalls.run, operation]) (Runs.next trivial rfl (rest anchors stack))

theorem branch (evaluated : Evaluates (globals := globals) module spec env condition heap value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (rest : BlockReturns (globals := globals) module spec env ((if flag then yes else no) ++ body) middle answer finalHeap) :
    BlockReturns (globals := globals) module spec env (.ifThen condition yes no :: body) heap answer finalHeap := by
  intro anchors stack
  exact Runs.next trivial rfl ((evaluated anchors _).trans
    (Runs.next trivial (by simp [HeapCalls.step, HeapCalls.run, truth]) (rest anchors stack)))

theorem while_loop (evaluated : Evaluates (globals := globals) module spec env condition heap value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (rest : BlockReturns (globals := globals) module spec env
      ((if flag then body ++ [Calls.loopContinuation body (.whileDo condition body otherwise)] else otherwise) ++ following)
      middle answer finalHeap) :
    BlockReturns (globals := globals) module spec env (.whileDo condition body otherwise :: following) heap answer finalHeap := by
  intro anchors stack
  exact Runs.next trivial rfl ((evaluated anchors _).trans
    (Runs.next trivial (by simp [HeapCalls.step, HeapCalls.run, truth]) (rest anchors stack)))

theorem function (plain : name ∉ module.memoizedFunctions)
    (found : findFunctionIn module.body name = some (args, body))
    (arguments : HeapCalls.completeArguments args values = some completed)
    (evaluated : BlockReturns (globals := globals) module spec
      (HeapCalls.functionEnv args body completed globals) (executableBody body) heap value finalHeap) :
    ReturnsValue (globals := globals) module spec name values heap value finalHeap := by
  intro anchors stack
  exact Runs.next plain (by simp [HeapCalls.step, found, arguments]) (evaluated anchors stack)

end BlockReturns

end FormalSW.PyAst.MemoHeapCalls
