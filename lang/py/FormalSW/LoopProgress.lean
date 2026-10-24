import lang.py.FormalSW.HeapCalls

/-! Supported divergence from finite, symbolic progress between loop boundaries. -/
namespace FormalSW.PyAst.HeapCalls

/-- Intermediate states can reach another invariant boundary; each boundary takes a real step. -/
theorem diverges_of_chunks {α : Type} (module : Module) (anchors : Nat)
    (globals : Mutable.Globals) (actual : State → Step State α)
    (liftNext : ∀ state following, step (globals := globals) module anchors state = .next following →
      actual state = .next following)
    (invariant : State → Prop) (entry : State)
    (initial : ∃ boundary, invariant boundary ∧ Reaches (globals := globals) module anchors entry boundary)
    (progress : ∀ boundary, invariant boundary → ∃ following next,
      step (globals := globals) module anchors boundary = .next following ∧
      Reaches (globals := globals) module anchors following next ∧ invariant next) :
    (Execution.mk State entry actual).Diverges := by
  let closed : State → Prop := fun state =>
    ∃ boundary, invariant boundary ∧ Reaches (globals := globals) module anchors state boundary
  refine ⟨closed, initial, ?_⟩
  intro state current
  obtain ⟨boundary, valid, reached⟩ := current
  cases reached with
  | refl =>
      obtain ⟨following, next, transition, rest, preserved⟩ := progress _ valid
      exact ⟨following, liftNext _ _ transition, next, preserved, rest⟩
  | next transition rest =>
      exact ⟨_, liftNext _ _ transition, boundary, valid, rest⟩

/-- A true while loop with a normally completing body makes a positive execution chunk. -/
theorem while_true_chunk (module : Module) (anchors : Nat) (globals : Mutable.Globals)
    (body following : List Stmt) (env finalEnv : Env) (heap finalHeap : Heap) (stack : List Frame)
    (plain : Calls.loopControl body = false)
    (continued : BlockContinues (globals := globals) module env body heap finalEnv finalHeap) :
    ∃ next, step (globals := globals) module anchors
        ⟨.block (.whileDo (.constant (.bool true)) body [] :: following) env, stack, heap⟩ = .next next ∧
      Reaches (globals := globals) module anchors next
        ⟨.block (.whileDo (.constant (.bool true)) body [] :: following) finalEnv, stack, finalHeap⟩ := by
  refine ⟨_, rfl, .next rfl ?_⟩
  apply Reaches.next (following :=
    ⟨.block (body ++ (.whileDo (.constant (.bool true)) body [] :: following)) env, stack, heap⟩)
  · simp [step, run, Mutable.truth, scalarTruth, Calls.loopContinuation, plain, List.append_assoc]
  · exact continued (.whileDo (.constant (.bool true)) body [] :: following) anchors stack

/-- Lift a preserved loop invariant to divergence of the complete scalar source call. -/
theorem scalar_while_diverges (module : Module) (name : String) (values : List Constant)
    (args : List Arg) (functionBody setup body : List Stmt) (supplied : List Mutable.Value)
    (found : findFunctionIn module.body name = some (args, functionBody))
    (arguments : completeArguments args (values.map Mutable.Value.scalar) = some supplied)
    (shape : executableBody functionBody = setup ++ [.whileDo (.constant (.bool true)) body []])
    (plain : Calls.loopControl body = false) (invariant : Env → Heap → Prop)
    (initialEnv : Env) (initialHeap : Heap)
    (initialized : BlockContinues module (functionEnv args functionBody supplied []) setup [] initialEnv initialHeap)
    (initial : invariant initialEnv initialHeap)
    (progress : ∀ env heap, invariant env heap → ∃ finalEnv finalHeap,
      BlockContinues module env body heap finalEnv finalHeap ∧ invariant finalEnv finalHeap) :
    (scalarFunction module name values).Diverges := by
  let boundary : Env → Heap → State := fun env heap =>
    ⟨.block [.whileDo (.constant (.bool true)) body []] env, [], heap⟩
  let valid : State → Prop := fun state =>
    ∃ env heap, invariant env heap ∧ state = boundary env heap
  apply diverges_of_chunks module 0 [] (scalarStep module)
    (fun state following transition => by simp [scalarStep, transition]) valid
  · refine ⟨boundary initialEnv initialHeap, ⟨initialEnv, initialHeap, initial, rfl⟩, ?_⟩
    apply Reaches.next (following :=
      ⟨.block (executableBody functionBody) (functionEnv args functionBody supplied []), [], []⟩)
    · simp [step, found, arguments]
    · simpa only [shape, boundary] using
        initialized [.whileDo (.constant (.bool true)) body []] 0 []
  · intro state current
    obtain ⟨env, heap, current, rfl⟩ := current
    obtain ⟨finalEnv, finalHeap, advanced, preserved⟩ := progress env heap current
    obtain ⟨following, transition, rest⟩ := while_true_chunk module 0 [] body [] env finalEnv heap finalHeap [] plain advanced
    exact ⟨following, boundary finalEnv finalHeap, transition, rest, finalEnv, finalHeap, preserved, rfl⟩

end FormalSW.PyAst.HeapCalls
