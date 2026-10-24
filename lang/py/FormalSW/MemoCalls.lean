import lang.py.FormalSW.Calls

/-! Scalar calls with unbounded memoization. Cache keys contain exact integer
arguments; cache observation and mutation are not exposed to source programs.
A miss evaluates the original body, including recursively memoized calls. Only
successful returns enter the cache; an exception unwinds without inserting it. -/

namespace FormalSW.PyAst.MemoCalls

structure Key where
  name : String
  arguments : List Int
deriving DecidableEq, BEq

abbrev Cache := Key → Option Constant
abbrev Specification := Key → Constant → Prop

def Cache.empty : Cache := fun _ => none

def Cache.insert (cache : Cache) (key : Key) (value : Constant) : Cache :=
  fun query => if query = key then some value else cache query

def Cache.Valid (spec : Specification) (cache : Cache) : Prop :=
  ∀ key value, cache key = some value → spec key value

theorem Cache.valid_empty (spec : Specification) : Valid spec empty := by
  intro key value found
  contradiction

theorem Cache.Valid.insert (valid : Valid spec cache) (correct : spec key value) :
    Valid spec (cache.insert key value) := by
  intro query result found
  by_cases same : query = key
  · subst query
    simp [Cache.insert] at found
    subst result
    exact correct
  · exact valid query result (by simpa [Cache.insert, same] using found)

/-- The caller's expression continuation is restored after caching a result. -/
structure Caller where
  key : Key
  stack : List Calls.Frame

structure State where
  current : Calls.State
  callers : List Caller
  cache : Cache

def integerArguments : List Constant → Option (List Int)
  | [] => some []
  | .int value :: rest => (value :: ·) <$> integerArguments rest
  | _ => none

@[simp] theorem integerArguments_map (values : List Int) :
    integerArguments (values.map Constant.int) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [integerArguments, ih]

private def advance (state : State) : Step Calls.State Constant → Step State Constant
  | .next current => .next { state with current }
  | .done result => .done result
  | .unsupported => .unsupported

def step (module : Module) (memoized : List String) (state : State) : Step State Constant :=
  match state.current with
  | ⟨.value value, []⟩ =>
      match state.callers with
      | [] => .done (.ok value)
      | caller :: callers =>
          .next ⟨⟨.value value, caller.stack⟩, callers, state.cache.insert caller.key value⟩
  | ⟨.invoke name values, stack⟩ =>
      if name ∈ memoized then
        match integerArguments values with
        | none => .unsupported
        | some arguments =>
            let key : Key := ⟨name, arguments⟩
            match state.cache key with
            | some value => .next { state with current := ⟨.value value, stack⟩ }
            | none =>
                match Calls.step module ⟨.invoke name values, []⟩ with
                | .next body => .next ⟨body, ⟨key, stack⟩ :: state.callers, state.cache⟩
                | .done result => .done result
                | .unsupported => .unsupported
      else advance state (Calls.step module state.current)
  | _ => advance state (Calls.step module state.current)

def function (module : Module) (memoized : List String) (name : String)
    (values : List Constant) (cache : Cache := Cache.empty) : Execution Constant :=
  ⟨State, ⟨⟨.invoke name values, []⟩, [], cache⟩, step module memoized⟩

def evaluate (module : Module) (memoized : List String) (env : ScalarEnv)
    (expression : Expr) (cache : Cache := Cache.empty) : Execution Constant :=
  ⟨State, ⟨⟨.expr expression env, []⟩, [], cache⟩, step module memoized⟩

/-- Preconditions execute in a private fresh cache and must return Boolean True. -/
def Condition (module : Module) (memoized : List String) (env : ScalarEnv) (expression : Expr) : Prop :=
  Finishes (evaluate module memoized env expression).step
    (evaluate module memoized env expression).initial (.ok (.bool true))

/-- Source contracts always use the cache wrappers recorded in the parsed module. -/
def sourceFunction (module : Module) (name : String) (values : List Constant) : Execution Constant :=
  function module module.memoizedFunctions name values

def sourceEvaluate (module : Module) (env : ScalarEnv) (expression : Expr) : Execution Constant :=
  evaluate module module.memoizedFunctions env expression

def SourceCondition (module : Module) (env : ScalarEnv) (expression : Expr) : Prop :=
  Condition module module.memoizedFunctions env expression

/-- Instructions that pass through the ordinary scalar interpreter unchanged. -/
def transparent (memoized : List String) : Calls.State → Prop
  | ⟨.invoke name _, _⟩ => name ∉ memoized
  | ⟨.value _, []⟩ => False
  | _ => True

theorem step_raw (plain : transparent memoized current)
    (transition : Calls.step module current = .next following) :
    step module memoized ⟨current, callers, cache⟩ = .next ⟨following, callers, cache⟩ := by
  rcases current with ⟨work, stack⟩
  cases work
  all_goals try { change advance _ (Calls.step module _) = _; rw [transition]; rfl }
  case value value =>
    cases stack with
    | nil => exact False.elim plain
    | cons frame frames =>
        change advance _ (Calls.step module _) = _
        rw [transition]
        rfl
  case invoke name values =>
    simp only [transparent] at plain
    simp only [step, if_neg plain]
    rw [transition]
    rfl

inductive Reaches (module : Module) (memoized : List String) : State → State → Prop where
  | refl : Reaches module memoized state state
  | next : step module memoized state = .next following →
      Reaches module memoized following final → Reaches module memoized state final

theorem Reaches.trans (run : Reaches module memoized a b)
    (rest : Reaches module memoized b c) : Reaches module memoized a c := by
  induction run with
  | refl => exact rest
  | next transition _ ih => exact .next transition (ih rest)

theorem Reaches.finishes (run : Reaches module memoized a b)
    (rest : Finishes (step module memoized) b result) :
    Finishes (step module memoized) a result := by
  induction run with
  | refl => exact rest
  | next transition _ ih => exact .next transition (ih rest)

/-- Runs preserve a semantic cache invariant in every surrounding call context. -/
def Runs (module : Module) (memoized : List String) (spec : Specification)
    (initial final : Calls.State) : Prop :=
  ∀ callers cache, cache.Valid spec → ∃ updated, updated.Valid spec ∧
    Reaches module memoized ⟨initial, callers, cache⟩ ⟨final, callers, updated⟩

namespace Runs

theorem refl : Runs module memoized spec state state :=
  fun _ cache valid => ⟨cache, valid, .refl⟩

theorem trans (run : Runs module memoized spec a b)
    (rest : Runs module memoized spec b c) : Runs module memoized spec a c := by
  intro callers cache valid
  obtain ⟨middle, valid, run⟩ := run callers cache valid
  obtain ⟨final, valid, rest⟩ := rest callers middle valid
  exact ⟨final, valid, run.trans rest⟩

theorem raw (plain : transparent memoized state)
    (transition : Calls.step module state = .next following) :
    Runs module memoized spec state following :=
  fun _ cache valid => ⟨cache, valid, .next (step_raw plain transition) .refl⟩

end Runs

def Evaluates (module : Module) (memoized : List String) (spec : Specification)
    (env : ScalarEnv) (expression : Expr) (value : Constant) : Prop :=
  ∀ stack, Runs module memoized spec ⟨.expr expression env, stack⟩ ⟨.value value, stack⟩

theorem Evaluates.finishes (run : Evaluates module memoized spec env expression value)
    (valid : cache.Valid spec) :
    Finishes (evaluate module memoized env expression cache).step
      (evaluate module memoized env expression cache).initial (.ok value) := by
  obtain ⟨_, _, reached⟩ := run [] [] cache valid
  exact reached.finishes (.done rfl)

theorem Evaluates.condition_iff (run : Evaluates module memoized spec env expression value) :
    Condition module memoized env expression ↔ value = .bool true := by
  have finished := run.finishes (Cache.valid_empty spec)
  constructor
  · intro holds
    exact Except.ok.inj (finished.unique holds)
  · intro equal
    subst value
    exact finished

def BlockReturns (module : Module) (memoized : List String) (spec : Specification)
    (env : ScalarEnv) (body : List Stmt) (value : Constant) : Prop :=
  ∀ stack, Runs module memoized spec ⟨.block body env, stack⟩ ⟨.value value, stack⟩

def ReturnsValue (module : Module) (memoized : List String) (spec : Specification)
    (name : String) (values : List Constant) (value : Constant) : Prop :=
  ∀ stack, Runs module memoized spec ⟨.invoke name values, stack⟩ ⟨.value value, stack⟩

theorem ReturnsValue.finishes (run : ReturnsValue module memoized spec name values value)
    (valid : cache.Valid spec) :
    Finishes (function module memoized name values cache).step
      (function module memoized name values cache).initial (.ok value) := by
  obtain ⟨_, _, reached⟩ := run [] [] cache valid
  exact reached.finishes (.done rfl)

theorem ReturnsValue.returns_cached (run : ReturnsValue module memoized spec name values value)
    (valid : cache.Valid spec) :
    (function module memoized name values cache).Returns := ⟨value, run.finishes valid⟩

theorem ReturnsValue.returns (run : ReturnsValue module memoized spec name values value) :
    (function module memoized name values).Returns := run.returns_cached (Cache.valid_empty spec)

namespace BlockReturns

theorem function (plain : name ∉ memoized)
    (found : findFunctionIn module.body name = some (args, body))
    (arity : args.length = values.length)
    (run : BlockReturns module memoized spec (argumentEnv args values) (executableBody body) value) :
    ReturnsValue module memoized spec name values value := by
  intro stack
  apply Runs.trans (b := ⟨.block (executableBody body) (argumentEnv args values), stack⟩)
  · exact Runs.raw plain (by simp [Calls.step, found, arity])
  · exact run stack

/-- Cache hits use the invariant; misses prove the body before inserting its result. -/
theorem memoized_function (cached : name ∈ memoized)
    (found : findFunctionIn module.body name = some (args, body))
    (arity : args.length = values.length)
    (run : BlockReturns module memoized spec (argumentEnv args (values.map Constant.int))
      (executableBody body) value)
    (correct : spec ⟨name, values⟩ value)
    (unique : ∀ other, spec ⟨name, values⟩ other → other = value) :
    ReturnsValue module memoized spec name (values.map Constant.int) value := by
  intro stack callers cache valid
  cases hit : cache ⟨name, values⟩ with
  | some other =>
      have equal := unique other (valid _ _ hit)
      subst other
      exact ⟨cache, valid, .next (by simp [step, cached, hit]) .refl⟩
  | none =>
      obtain ⟨updated, preserved, bodyRun⟩ := run [] (⟨⟨name, values⟩, stack⟩ :: callers) cache valid
      refine ⟨updated.insert ⟨name, values⟩ value, preserved.insert correct, ?_⟩
      exact .next (by simp [step, cached, hit, Calls.step, found, arity])
        (bodyRun.trans (.next rfl .refl))

end BlockReturns
end FormalSW.PyAst.MemoCalls
