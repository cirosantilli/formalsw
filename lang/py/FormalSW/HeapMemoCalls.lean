import lang.py.FormalSW.HeapCalls
import lang.py.FormalSW.MemoCalls

/-! Unbounded memoization with heap values. Cache entries retain original references;
misses execute the original heap body and recursively share the same cache. -/
namespace FormalSW.PyAst.HeapMemoCalls
abbrev Value := Mutable.Value
abbrev Heap := Mutable.Heap
abbrev Env := Mutable.Env
abbrev Completion := Mutable.Completion
abbrev Key := MemoCalls.Key
abbrev Cache := Key → Option Value
abbrev Specification := Heap → Key → Value → Prop

def Cache.empty : Cache := fun _ => none

def Cache.insert (cache : Cache) (key : Key) (value : Value) : Cache :=
  fun query => if query = key then some value else cache query

def Cache.Valid (spec : Specification) (heap : Heap) (cache : Cache) : Prop :=
  ∀ key value, cache key = some value → spec heap key value

def Cache.Preserves (spec : Specification) (before after : Heap) : Prop :=
  ∀ (cache : Cache), cache.Valid spec before → cache.Valid spec after

theorem Cache.valid_empty (spec : Specification) (heap : Heap) : Valid spec heap empty := by
  intro key value found
  contradiction

theorem Cache.Valid.insert (valid : Valid spec heap cache) (correct : spec heap key value) :
    Valid spec heap (cache.insert key value) := by
  intro query result found
  by_cases same : query = key
  · subst query
    simp [Cache.insert] at found
    subst result
    exact correct
  · exact valid query result (by simpa [Cache.insert, same] using found)

theorem Cache.Preserves.refl : Preserves spec heap heap := fun _ valid => valid

theorem Cache.Preserves.trans (first : Preserves spec before middle)
    (second : Preserves spec middle after) : Preserves spec before after :=
  fun cache valid => second cache (first cache valid)

/-- Useful for invariants of immutable cached tuples under unrelated allocations. -/
theorem Cache.preserves_append
    (stable : ∀ key value, spec heap key value → spec (heap ++ extra) key value) :
    Preserves spec heap (heap ++ extra) :=
  fun _ valid key value found => stable key value (valid key value found)

structure Caller where
  key : Key
  stack : List HeapCalls.Frame

structure State where
  current : HeapCalls.State
  callers : List Caller
  cache : Cache

def integerArguments : List Value → Option (List Int)
  | [] => some []
  | .scalar (.int value) :: rest => (value :: ·) <$> integerArguments rest
  | _ => none

@[simp] theorem integerArguments_map (values : List Int) :
    integerArguments (values.map (fun value => Mutable.Value.scalar (.int value))) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [integerArguments, ih]

/-- Private source encoding for a protected compiler tuple constant. -/
def pooledTuple (identity : String) (items : List Expr) : Expr :=
  .consumeGenerator (.call (.name "$formalsw.constant.tuple") [.constant (.string identity)]) (.tuple items) []

def pooledTupleParts : Expr → Option (String × List Expr)
  | .consumeGenerator (.call (.name "$formalsw.constant.tuple") [.constant (.string identity)]) (.tuple items) [] =>
      some (identity, items)
  | _ => none

def pooledIdentity (expression : Expr) : Option String := (pooledTupleParts expression).map Prod.fst

def literalKey (identity : String) : Key := ⟨"$formalsw.constant.tuple:" ++ identity, []⟩

/-- Source proofs can name compiler-derived keys without embedding a source hash. -/
def pooledKey (expression : Expr) : Option Key := (pooledIdentity expression).map literalKey

theorem pooledTupleParts_eq_some (found : pooledTupleParts expression = some (identity, items)) :
    expression = pooledTuple identity items := by
  unfold pooledTupleParts at found
  split at found <;> simp_all [pooledTuple]

theorem pooled_unsupported {globals : Mutable.Globals} (found : pooledTupleParts expression = some (identity, items)) :
    HeapCalls.step (globals := globals) module anchors ⟨.expr expression env, stack, heap⟩ = .unsupported := by
  rw [pooledTupleParts_eq_some found]
  rfl

private def advance (state : State) : Step HeapCalls.State Completion → Step State Completion
  | .next current => .next { state with current }
  | .done outcome => .done outcome
  | .unsupported => .unsupported

/-- Saved miss continuations remain part of the surrounding generator boundary. -/
def protectGenerator (state : State) : Step State Completion → Step State Completion
  | .done (.ok completion) => .done (.ok { completion with outcome := match completion.outcome with
      | .error error => .error (Calls.generatorException
          (state.current.stack.any HeapCalls.Frame.inGenerator ||
            state.callers.any (fun caller => caller.stack.any HeapCalls.Frame.inGenerator)) error)
      | .ok value => .ok value })
  | transition => transition

@[simp] theorem protectGenerator_next (state next : State) :
    protectGenerator state (.next next) = .next next := rfl

@[simp] theorem protectGenerator_unsupported (state : State) :
    protectGenerator state .unsupported = .unsupported := rfl

def step (module : Module) (anchors : Nat) (state : State)
    (globals : Mutable.Globals := []) : Step State Completion :=
  protectGenerator state <|
  match state.current with
  | ⟨.expr expression env, stack, heap⟩ =>
      match pooledTupleParts expression with
      | some (identity, items) =>
          let key := literalKey identity
          match state.cache key with
          | some value => .next { state with current := ⟨.value value, stack, heap⟩ }
          | none => .next ⟨⟨.expr (.tuple items) env, [], heap⟩,
              ⟨key, stack⟩ :: state.callers, state.cache⟩
      | none => advance state (HeapCalls.step (globals := globals) module anchors state.current)
  | ⟨.value value, [], heap⟩ =>
      match state.callers with
      | [] => .done (.ok ⟨.ok value, globals, heap, anchors⟩)
      | caller :: callers =>
          .next ⟨⟨.value value, caller.stack, heap⟩, callers, state.cache.insert caller.key value⟩
  | ⟨.operation (.call name) values, stack, heap⟩ =>
      if name ∈ module.memoizedFunctions then
        match integerArguments values with
        | none => .unsupported
        | some arguments =>
            let key : Key := ⟨name, arguments⟩
            match state.cache key with
            | some value => .next { state with current := ⟨.value value, stack, heap⟩ }
            | none =>
                match HeapCalls.step (globals := globals) module anchors ⟨.operation (.call name) values, [], heap⟩ with
                | .next body => .next ⟨body, ⟨key, stack⟩ :: state.callers, state.cache⟩
                | .done result => .done result
                | .unsupported => .unsupported
      else advance state (HeapCalls.step (globals := globals) module anchors state.current)
  | _ => advance state (HeapCalls.step (globals := globals) module anchors state.current)

def call (module : Module) (name : String) (values : List Value) (heap : Heap)
    (globals : Mutable.Globals := []) : Mutable.Call :=
  ⟨⟨State, ⟨⟨.operation (.call name) values, [], heap⟩, [], Cache.empty⟩,
    step (globals := globals) module heap.length⟩⟩

def evaluate (module : Module) (env : Env) (expression : Expr) (heap : Heap)
    (globals : Mutable.Globals := []) : Mutable.Call :=
  ⟨⟨State, ⟨⟨.expr expression env, [], heap⟩, [], Cache.empty⟩,
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
  ⟨State, ⟨⟨.operation (.call name) (values.map Mutable.Value.scalar), [], []⟩, [], Cache.empty⟩,
    scalarStep module⟩

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

/-- Relational runs permit cache hits to reuse arbitrary existing object addresses. -/
def RunsRel (module : Module) (spec : Specification) (anchors : Nat)
    (initial : HeapCalls.State) (post : HeapCalls.State → Prop)
    (globals : Mutable.Globals := []) : Prop :=
  ∀ callers cache, cache.Valid spec initial.heap → ∃ final updated,
    post final ∧ updated.Valid spec final.heap ∧
      Reaches (globals := globals) module anchors ⟨initial, callers, cache⟩ ⟨final, callers, updated⟩

def Runs (module : Module) (spec : Specification) (anchors : Nat)
    (initial final : HeapCalls.State) (globals : Mutable.Globals := []) : Prop :=
  RunsRel (globals := globals) module spec anchors initial (fun result => result = final)

namespace RunsRel

theorem refl (holds : post state) : RunsRel (globals := globals) module spec anchors state post :=
  fun _ cache valid => ⟨state, cache, holds, valid, .refl⟩

theorem bind (first : RunsRel (globals := globals) module spec anchors initial middle)
    (rest : ∀ state, middle state → RunsRel (globals := globals) module spec anchors state post) :
    RunsRel (globals := globals) module spec anchors initial post := by
  intro callers cache valid
  obtain ⟨state, cache, holds, valid, first⟩ := first callers cache valid
  obtain ⟨final, cache, holds, valid, rest⟩ := rest state holds callers cache valid
  exact ⟨final, cache, holds, valid, first.trans rest⟩

theorem consequence (run : RunsRel (globals := globals) module spec anchors initial pre)
    (weaken : ∀ state, pre state → post state) :
    RunsRel (globals := globals) module spec anchors initial post := by
  intro callers cache valid
  obtain ⟨final, cache, holds, valid, reached⟩ := run callers cache valid
  exact ⟨final, cache, weaken final holds, valid, reached⟩

end RunsRel

namespace Runs

theorem refl : Runs (globals := globals) module spec anchors state state := RunsRel.refl rfl

theorem trans (first : Runs (globals := globals) module spec anchors a b)
    (second : Runs (globals := globals) module spec anchors b c) :
    Runs (globals := globals) module spec anchors a c :=
  first.bind (fun state same => by subst state; exact second)

end Runs

/-- Postconditions describe the actual returned value and actual resulting heap. -/
def ValuePost (stack : List HeapCalls.Frame) (post : Value → Heap → Prop)
    (final : HeapCalls.State) : Prop :=
  ∃ value heap, final = ⟨.value value, stack, heap⟩ ∧ post value heap

def EvaluatesRel (module : Module) (spec : Specification) (env : Env) (expression : Expr)
    (heap : Heap) (post : Value → Heap → Prop) (globals : Mutable.Globals := []) : Prop :=
  ∀ anchors stack, RunsRel (globals := globals) module spec anchors ⟨.expr expression env, stack, heap⟩ (ValuePost stack post)

def ReturnsRel (module : Module) (spec : Specification) (name : String) (values : List Value)
    (heap : Heap) (post : Value → Heap → Prop) (globals : Mutable.Globals := []) : Prop :=
  ∀ anchors stack, RunsRel (globals := globals) module spec anchors ⟨.operation (.call name) values, stack, heap⟩ (ValuePost stack post)

def BlockReturnsRel (module : Module) (spec : Specification) (env : Env) (body : List Stmt)
    (heap : Heap) (post : Value → Heap → Prop) (globals : Mutable.Globals := []) : Prop :=
  ∀ anchors stack, RunsRel (globals := globals) module spec anchors ⟨.block body env, stack, heap⟩ (ValuePost stack post)

def Evaluates (module : Module) (spec : Specification) (env : Env) (expression : Expr)
    (heap : Heap) (value : Value) (finalHeap : Heap) (globals : Mutable.Globals := []) : Prop :=
  ∀ anchors stack, Runs (globals := globals) module spec anchors ⟨.expr expression env, stack, heap⟩ ⟨.value value, stack, finalHeap⟩

def ReturnsValue (module : Module) (spec : Specification) (name : String) (values : List Value)
    (heap : Heap) (value : Value) (finalHeap : Heap) (globals : Mutable.Globals := []) : Prop :=
  ∀ anchors stack, Runs (globals := globals) module spec anchors ⟨.operation (.call name) values, stack, heap⟩ ⟨.value value, stack, finalHeap⟩

def BlockReturns (module : Module) (spec : Specification) (env : Env) (body : List Stmt)
    (heap : Heap) (value : Value) (finalHeap : Heap) (globals : Mutable.Globals := []) : Prop :=
  ∀ anchors stack, Runs (globals := globals) module spec anchors ⟨.block body env, stack, heap⟩ ⟨.value value, stack, finalHeap⟩

/-- Instructions delegated unchanged to the ordinary heap interpreter. -/
def transparent (module : Module) (state : HeapCalls.State) : Prop :=
  match state.work, state.stack with
  | .operation (.call name) _, _ => name ∉ module.memoizedFunctions
  | .value _, [] => False
  | .expr expression _, _ => pooledTupleParts expression = none
  | _, _ => True

theorem step_raw (plain : transparent module current)
    (transition : HeapCalls.step (globals := globals) module anchors current = .next following) :
    step (globals := globals) module anchors ⟨current, callers, cache⟩ =
      .next ⟨following, callers, cache⟩ := by
  rcases current with ⟨work, stack, heap⟩
  cases work
  all_goals try { change protectGenerator _ (advance _ (HeapCalls.step (globals := globals) module anchors _)) = _; rw [transition]; rfl }
  case expr expression env =>
    simp only [transparent] at plain
    simp only [step, plain]
    rw [transition]
    rfl
  case value value =>
    cases stack with
    | nil => exact False.elim plain
    | cons frame frames =>
        change protectGenerator _ (advance _ (HeapCalls.step (globals := globals) module anchors _)) = _
        rw [transition]
        rfl
  case operation operation values =>
    cases operation
    all_goals try { change protectGenerator _ (advance _ (HeapCalls.step (globals := globals) module anchors _)) = _; rw [transition]; rfl }
    case call name =>
      simp only [transparent] at plain
      simp only [step, if_neg plain]
      rw [transition]
      rfl

@[simp] theorem argumentsState_heap (operation : HeapCalls.Operation) (env : Env) (done : List Value)
    (expressions : List Expr) (stack : List HeapCalls.Frame) (heap : Heap) :
    (HeapCalls.argumentsState operation env done expressions stack heap).heap = heap := by
  cases expressions <;> rfl

namespace Runs

theorem raw (plain : transparent module current)
    (transition : HeapCalls.step (globals := globals) module anchors current = .next following)
    (preserved : Cache.Preserves spec current.heap following.heap := by intro cache valid; simpa using valid) :
    Runs (globals := globals) module spec anchors current following := by
  intro callers cache valid
  exact ⟨following, cache, rfl, preserved cache valid, .next (step_raw plain transition) .refl⟩

theorem next (plain : transparent module current)
    (transition : HeapCalls.step (globals := globals) module anchors current = .next following)
    (rest : Runs (globals := globals) module spec anchors following final)
    (preserved : Cache.Preserves spec current.heap following.heap := by intro cache valid; simpa using valid) :
    Runs (globals := globals) module spec anchors current final := (raw plain transition preserved).trans rest

end Runs

namespace RunsRel

theorem next (plain : transparent module current)
    (transition : HeapCalls.step (globals := globals) module anchors current = .next following)
    (rest : RunsRel (globals := globals) module spec anchors following post)
    (preserved : Cache.Preserves spec current.heap following.heap := by intro cache valid; simpa using valid) :
    RunsRel (globals := globals) module spec anchors current post :=
  (Runs.raw plain transition preserved).bind (fun state same => by subst state; exact rest)

end RunsRel

theorem Evaluates.rel (run : Evaluates (globals := globals) module spec env expression heap value after) :
    EvaluatesRel (globals := globals) module spec env expression heap (fun result final => result = value ∧ final = after) := by
  intro anchors stack
  exact (run anchors stack).consequence (by intro final same; subst final; exact ⟨value, after, rfl, rfl, rfl⟩)

theorem ReturnsValue.rel (run : ReturnsValue (globals := globals) module spec name values heap value after) :
    ReturnsRel (globals := globals) module spec name values heap (fun result final => result = value ∧ final = after) := by
  intro anchors stack
  exact (run anchors stack).consequence (by intro final same; subst final; exact ⟨value, after, rfl, rfl, rfl⟩)

theorem BlockReturns.rel (run : BlockReturns (globals := globals) module spec env body heap value after) :
    BlockReturnsRel (globals := globals) module spec env body heap (fun result final => result = value ∧ final = after) := by
  intro anchors stack
  exact (run anchors stack).consequence (by intro final same; subst final; exact ⟨value, after, rfl, rfl, rfl⟩)

theorem EvaluatesRel.consequence (run : EvaluatesRel (globals := globals) module spec env expression heap pre)
    (weaken : ∀ value after, pre value after → post value after) :
    EvaluatesRel (globals := globals) module spec env expression heap post := by
  intro anchors stack
  apply (run anchors stack).consequence
  rintro final ⟨value, after, rfl, holds⟩
  exact ⟨value, after, rfl, weaken value after holds⟩

theorem ReturnsRel.consequence (run : ReturnsRel (globals := globals) module spec name values heap pre)
    (weaken : ∀ value after, pre value after → post value after) :
    ReturnsRel (globals := globals) module spec name values heap post := by
  intro anchors stack
  apply (run anchors stack).consequence
  rintro final ⟨value, after, rfl, holds⟩
  exact ⟨value, after, rfl, weaken value after holds⟩

theorem BlockReturnsRel.consequence (run : BlockReturnsRel (globals := globals) module spec env body heap pre)
    (weaken : ∀ value after, pre value after → post value after) :
    BlockReturnsRel (globals := globals) module spec env body heap post := by
  intro anchors stack
  apply (run anchors stack).consequence
  rintro final ⟨value, after, rfl, holds⟩
  exact ⟨value, after, rfl, weaken value after holds⟩

/-- Hits use the current heap invariant; misses execute the source body and insert only its actual return. -/
theorem BlockReturnsRel.memoized_function (cached : name ∈ module.memoizedFunctions)
    (found : findFunctionIn module.body name = some (args, body))
    (arguments : HeapCalls.completeArguments args (values.map (fun value => Mutable.Value.scalar (.int value))) = some completed)
    (run : BlockReturnsRel (globals := globals) module spec (HeapCalls.functionEnv args body completed globals)
      (executableBody body) heap (fun value after => post value after ∧ spec after ⟨name, values⟩ value))
    (hit : ∀ value, spec heap ⟨name, values⟩ value → post value heap) :
    ReturnsRel (globals := globals) module spec name (values.map (fun value => Mutable.Value.scalar (.int value))) heap post := by
  intro anchors stack callers cache valid
  cases cachedValue : cache ⟨name, values⟩ with
  | some value =>
      exact ⟨⟨.value value, stack, heap⟩, cache,
        ⟨value, heap, rfl, hit value (valid _ _ cachedValue)⟩, valid,
        .next (by simp [step, cached, cachedValue]) .refl⟩
  | none =>
      obtain ⟨final, updated, ⟨value, after, same, holds, correct⟩, preserved, reached⟩ :=
        run anchors [] (⟨⟨name, values⟩, stack⟩ :: callers) cache valid
      subst final
      refine ⟨⟨.value value, stack, after⟩, updated.insert ⟨name, values⟩ value,
        ⟨value, after, rfl, holds⟩, preserved.insert correct, ?_⟩
      exact .next (by simp [step, cached, cachedValue, HeapCalls.step, found, arguments])
        (reached.trans (.next rfl .refl))

theorem ReturnsRel.finishes (run : ReturnsRel (globals := globals) module spec name values heap post) :
    ∃ value after, post value after ∧
      (call (globals := globals) module name values heap).Finishes ⟨.ok value, globals, after, heap.length⟩ := by
  obtain ⟨final, cache, ⟨value, after, same, holds⟩, _, reached⟩ :=
    run heap.length [] [] Cache.empty (Cache.valid_empty spec heap)
  subst final
  exact ⟨value, after, holds, reached.finishes (.done rfl)⟩

theorem ReturnsRel.returns (run : ReturnsRel (globals := globals) module spec name values heap post) :
    (call (globals := globals) module name values heap).Returns := by
  obtain ⟨value, after, _, finished⟩ := run.finishes
  exact ⟨value, globals, after, heap.length, finished⟩

theorem EvaluatesRel.finishes (run : EvaluatesRel (globals := globals) module spec env expression heap post) :
    ∃ value after, post value after ∧
      (evaluate (globals := globals) module env expression heap).Finishes ⟨.ok value, globals, after, heap.length⟩ := by
  obtain ⟨final, cache, ⟨value, after, same, holds⟩, _, reached⟩ :=
    run heap.length [] [] Cache.empty (Cache.valid_empty spec heap)
  subst final
  exact ⟨value, after, holds, reached.finishes (.done rfl)⟩

theorem Reaches.scalar_finishes (run : Reaches module 0 a b)
    (rest : Finishes (scalarStep module) b outcome) : Finishes (scalarStep module) a outcome := by
  generalize empty : ([] : Mutable.Globals) = context at run
  induction run with
  | refl => exact rest
  | next transition _ ih =>
      cases empty
      exact .next (by simp [scalarStep, transition]) (ih rest rfl)

theorem ReturnsRel.scalar_finishes {post : Heap → Prop}
    (run : ReturnsRel module spec name (values.map Mutable.Value.scalar) []
      (fun value after => value = .scalar result ∧ post after)) :
    ∃ after, post after ∧ Finishes (scalarFunction module name values).step
      (scalarFunction module name values).initial (.ok result) := by
  obtain ⟨final, cache, ⟨value, after, same, equal, holds⟩, _, reached⟩ :=
    run 0 [] [] Cache.empty (Cache.valid_empty spec [])
  subst final
  subst value
  exact ⟨after, holds, reached.scalar_finishes (.done rfl)⟩

theorem ReturnsRel.scalar_returns {post : Heap → Prop}
    (run : ReturnsRel module spec name (values.map Mutable.Value.scalar) []
      (fun value after => value = .scalar result ∧ post after)) :
    (scalarFunction module name values).Returns := by
  obtain ⟨_, _, finished⟩ := run.scalar_finishes
  exact ⟨result, finished⟩

/-- Compiler tuple constants share their actual heap object across all source users. -/
theorem EvaluatesRel.pooled_tuple
    (run : EvaluatesRel (globals := globals) module spec env (.tuple items) heap
      (fun value after => post value after ∧ spec after (literalKey identity) value))
    (hit : ∀ value, spec heap (literalKey identity) value → post value heap) :
    EvaluatesRel (globals := globals) module spec env (pooledTuple identity items) heap post := by
  intro anchors stack callers cache valid
  cases cachedValue : cache (literalKey identity) with
  | some value =>
      exact ⟨⟨.value value, stack, heap⟩, cache,
        ⟨value, heap, rfl, hit value (valid _ _ cachedValue)⟩, valid,
        .next (by simp [step, pooledTuple, pooledTupleParts, cachedValue]) .refl⟩
  | none =>
      obtain ⟨final, updated, ⟨value, after, same, holds, correct⟩, preserved, reached⟩ :=
        run anchors [] (⟨literalKey identity, stack⟩ :: callers) cache valid
      subst final
      refine ⟨⟨.value value, stack, after⟩, updated.insert (literalKey identity) value,
        ⟨value, after, rfl, holds⟩, preserved.insert correct, ?_⟩
      exact .next (by simp [step, pooledTuple, pooledTupleParts, cachedValue])
        (reached.trans (.next rfl .refl))

end FormalSW.PyAst.HeapMemoCalls
