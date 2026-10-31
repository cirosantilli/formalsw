import lang.py.FormalSW.MemoCallRules

/-! Symbolic progress of scalar loops whose helper calls share a memoization cache. -/
namespace FormalSW.PyAst.MemoCalls

def BlockContinues (module : Module) (memoized : List String) (spec : Specification)
    (env : ScalarEnv) (body : List Stmt) (finalEnv : ScalarEnv) : Prop :=
  ∀ following stack, Runs module memoized spec
    ⟨.block (body ++ following) env, stack⟩ ⟨.block following finalEnv, stack⟩

namespace BlockContinues

theorem nil : BlockContinues module memoized spec env [] env := fun _ _ => Runs.refl

theorem append (first : BlockContinues module memoized spec env body middleEnv)
    (second : BlockContinues module memoized spec middleEnv rest finalEnv) :
    BlockContinues module memoized spec env (body ++ rest) finalEnv := by
  intro following stack
  simpa only [List.append_assoc] using
    (first (rest ++ following) stack).trans (second following stack)

theorem assign (evaluated : Evaluates module memoized spec env expression value) :
    BlockContinues module memoized spec env [.assign [.name name] expression] (env.set name value) := by
  intro following stack
  exact Runs.next (by trivial) rfl ((evaluated _).trans (Runs.raw (by trivial) rfl))

theorem augAssign (evaluated : Evaluates module memoized spec env (.binOp (.name name) op expression) value) :
    BlockContinues module memoized spec env [.augAssign (.name name) op expression] (env.set name value) := by
  intro following stack
  exact Runs.next (by trivial) rfl ((evaluated _).trans (Runs.raw (by trivial) rfl))

theorem branch (evaluated : Evaluates module memoized spec env condition value)
    (executed : BlockContinues module memoized spec env (if scalarTruth value then yes else no) finalEnv) :
    BlockContinues module memoized spec env [.ifThen condition yes no] finalEnv := by
  intro following stack
  exact Runs.next (by trivial) rfl ((evaluated _).trans
    (Runs.next (by trivial) (by simp [Calls.step]) (executed following stack)))

theorem returns (first : BlockContinues module memoized spec env body finalEnv)
    (rest : BlockReturns module memoized spec finalEnv following value) :
    BlockReturns module memoized spec env (body ++ following) value :=
  fun stack => (first following stack).trans (rest stack)

end BlockContinues

theorem diverges_of_chunks (module : Module) (memoized : List String)
    (invariant : State → Prop) (entry : State)
    (initial : ∃ boundary, invariant boundary ∧ Reaches module memoized entry boundary)
    (progress : ∀ boundary, invariant boundary → ∃ following next,
      step module memoized boundary = .next following ∧
      Reaches module memoized following next ∧ invariant next) :
    (Execution.mk State entry (step module memoized)).Diverges := by
  let closed : State → Prop := fun state =>
    ∃ boundary, invariant boundary ∧ Reaches module memoized state boundary
  refine ⟨closed, initial, ?_⟩
  intro state current
  obtain ⟨boundary, valid, reached⟩ := current
  cases reached with
  | refl =>
      obtain ⟨following, next, transition, rest, preserved⟩ := progress _ valid
      exact ⟨following, transition, next, preserved, rest⟩
  | next transition rest => exact ⟨_, transition, boundary, valid, rest⟩

/-- A complete body preserves cache validity, while the loop boundary makes a real step. -/
theorem while_true_chunk (module : Module) (memoized : List String) (spec : Specification)
    (body following : List Stmt) (env finalEnv : ScalarEnv) (stack : List Calls.Frame)
    (callers : List Caller) (cache : Cache) (valid : cache.Valid spec)
    (plain : Calls.loopControl body = false)
    (continued : BlockContinues module memoized spec env body finalEnv) :
    ∃ next updated, updated.Valid spec ∧
      step module memoized
        ⟨⟨.block (.whileDo (.constant (.bool true)) body [] :: following) env, stack⟩, callers, cache⟩ = .next next ∧
      Reaches module memoized next
        ⟨⟨.block (.whileDo (.constant (.bool true)) body [] :: following) finalEnv, stack⟩, callers, updated⟩ := by
  have rest : Runs module memoized spec
      ⟨.expr (.constant (.bool true)) env,
        .branch (body ++ [Calls.loopContinuation body (.whileDo (.constant (.bool true)) body [])]) [] following env :: stack⟩
      ⟨.block (.whileDo (.constant (.bool true)) body [] :: following) finalEnv, stack⟩ := by
    apply Runs.next (by trivial) rfl
    apply Runs.next (following :=
      ⟨.block (body ++ (.whileDo (.constant (.bool true)) body [] :: following)) env, stack⟩) (by trivial)
      (by simp [Calls.step, scalarTruth, Calls.loopContinuation, plain, List.append_assoc])
    exact continued (.whileDo (.constant (.bool true)) body [] :: following) stack
  obtain ⟨updated, preserved, reached⟩ := rest callers cache valid
  exact ⟨_, updated, preserved, step_raw (by trivial) rfl, reached⟩

/-- Initialization and normally completing cached iterations establish supported divergence. -/
theorem scalar_while_diverges (module : Module) (memoized : List String) (spec : Specification)
    (name : String) (values : List Constant) (args : List Arg) (functionBody setup body : List Stmt)
    (uncached : name ∉ memoized)
    (found : findFunctionIn module.body name = some (args, functionBody))
    (arity : args.length = values.length)
    (shape : executableBody functionBody = setup ++ [.whileDo (.constant (.bool true)) body []])
    (plain : Calls.loopControl body = false) (invariant : ScalarEnv → Prop) (initialEnv : ScalarEnv)
    (initialized : BlockContinues module memoized spec (argumentEnv args values) setup initialEnv)
    (initial : invariant initialEnv)
    (progress : ∀ env, invariant env → ∃ finalEnv,
      BlockContinues module memoized spec env body finalEnv ∧ invariant finalEnv) :
    (function module memoized name values).Diverges := by
  let boundary : ScalarEnv → Cache → State := fun env cache =>
    ⟨⟨.block [.whileDo (.constant (.bool true)) body []] env, []⟩, [], cache⟩
  let valid : State → Prop := fun state =>
    ∃ env cache, invariant env ∧ cache.Valid spec ∧ state = boundary env cache
  apply diverges_of_chunks module memoized valid
  · have entered : Runs module memoized spec ⟨.invoke name values, []⟩
        ⟨.block (executableBody functionBody) (argumentEnv args values), []⟩ :=
      Runs.raw uncached (by simp [Calls.step, found, arity])
    have setupRun : Runs module memoized spec ⟨.invoke name values, []⟩
        ⟨.block [.whileDo (.constant (.bool true)) body []] initialEnv, []⟩ := by
      apply entered.trans
      simpa only [shape] using initialized [.whileDo (.constant (.bool true)) body []] []
    obtain ⟨updated, preserved, reached⟩ := setupRun [] Cache.empty (Cache.valid_empty spec)
    exact ⟨boundary initialEnv updated, ⟨initialEnv, updated, initial, preserved, rfl⟩, reached⟩
  · intro state current
    obtain ⟨env, cache, current, preserved, rfl⟩ := current
    obtain ⟨finalEnv, advanced, holds⟩ := progress env current
    obtain ⟨following, updated, cacheValid, transition, reached⟩ :=
      while_true_chunk module memoized spec body [] env finalEnv [] [] cache preserved plain advanced
    exact ⟨following, boundary finalEnv updated, transition, reached, finalEnv, updated, holds, cacheValid, rfl⟩

end FormalSW.PyAst.MemoCalls
