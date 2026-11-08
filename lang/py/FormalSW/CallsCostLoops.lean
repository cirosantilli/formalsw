import lang.py.FormalSW.CallsCost

/-! Compositional costs for library calls and statement loops. Costs count scalar
interpreter transitions: library operations and integer arithmetic are atomic. -/
namespace FormalSW.PyAst.Calls.Cost

namespace EvaluatesIn

theorem library_pair (left : EvaluatesIn module env a ca av)
    (right : EvaluatesIn module env b cb bv)
    (absent : findFunctionIn module.body name = none)
    (result : libraryCall module name [av, bv] = some (.ok value)) :
    EvaluatesIn module env (.call (.name name) [a, b]) (ca + cb + 4) value := by
  intro stack
  have run := ReachesIn.next (step := step module)
    (state := ⟨.expr (.call (.name name) [a, b]) env, stack⟩) rfl
    ((left _).trans (.next rfl ((right _).trans (.next rfl
      (.next (following := ⟨.value value, stack⟩) (by simp [step, absent, outcome, result]) .refl)))))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem compare (left : EvaluatesIn module env a ca av)
    (right : EvaluatesIn module env b cb bv)
    (result : scalarCompare op av bv = some value) :
    EvaluatesIn module env (.compare a [(op, b)]) (ca + cb + 3) (.bool value) := by
  intro stack
  have run := ReachesIn.next (step := step module)
    (state := ⟨.expr (.compare a [(op, b)]) env, stack⟩) rfl
    ((left _).trans (.next rfl ((right _).trans
      (.next (following := ⟨.value (.bool value), stack⟩) (by simp [step, outcome, result]) .refl))))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

end EvaluatesIn

/-- An assignment evaluates its right-hand side and installs its value. -/
theorem assign (evaluated : EvaluatesIn module env expression cost value)
    (name : String) (following : List Stmt) (stack : List Frame) :
    ReachesIn (step module)
      ⟨.block (.assign [.name name] expression :: following) env, stack⟩ (cost + 2)
      ⟨.block following (env.set name value), stack⟩ := by
  have run := ReachesIn.next (step := step module)
    (state := ⟨.block (.assign [.name name] expression :: following) env, stack⟩)
    rfl ((evaluated _).trans (.next rfl .refl))
  simpa [Nat.add_assoc] using run

theorem augAssign (evaluated : EvaluatesIn module env (.binOp (.name name) op expression) cost value)
    (following : List Stmt) (stack : List Frame) :
    ReachesIn (step module)
      ⟨.block (.augAssign (.name name) op expression :: following) env, stack⟩ (cost + 2)
      ⟨.block following (env.set name value), stack⟩ := by
  have run := ReachesIn.next (step := step module)
    (state := ⟨.block (.augAssign (.name name) op expression :: following) env, stack⟩)
    rfl ((evaluated _).trans (.next rfl .refl))
  simpa [Nat.add_assoc] using run

theorem unpackPair (left : EvaluatesIn module env a ca av)
    (right : EvaluatesIn module env b cb bv) (first second : String)
    (following : List Stmt) (stack : List Frame) :
    ReachesIn (step module)
      ⟨.block (.assign [.tuple [.name first, .name second]] (.tuple [a, b]) :: following) env, stack⟩
      (ca + cb + 3) ⟨.block following ((env.set first av).set second bv), stack⟩ := by
  have run := ReachesIn.next (step := step module)
    (state := ⟨.block (.assign [.tuple [.name first, .name second]] (.tuple [a, b]) :: following) env, stack⟩)
    rfl ((left _).trans (.next rfl ((right _).trans (.next rfl .refl))))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem branch (evaluated : EvaluatesIn module env condition cost (.bool test))
    (yes no following : List Stmt) (stack : List Frame) :
    ReachesIn (step module) ⟨.block (.ifThen condition yes no :: following) env, stack⟩
      (cost + 2) ⟨.block ((if test then yes else no) ++ following) env, stack⟩ := by
  have run := ReachesIn.next (step := step module)
    (state := ⟨.block (.ifThen condition yes no :: following) env, stack⟩)
    rfl ((evaluated _).trans (.next rfl .refl))
  simpa [Nat.add_assoc] using run

theorem whileTest (evaluated : EvaluatesIn module env condition cost (.bool test))
    (body otherwise following : List Stmt) (stack : List Frame) :
    ReachesIn (step module) ⟨.block (.whileDo condition body otherwise :: following) env, stack⟩
      (cost + 2)
      ⟨.block ((if test then body ++ [loopContinuation body (.whileDo condition body otherwise)]
        else otherwise) ++ following) env, stack⟩ := by
  have run := ReachesIn.next (step := step module)
    (state := ⟨.block (.whileDo condition body otherwise :: following) env, stack⟩)
    rfl ((evaluated _).trans (.next rfl .refl))
  simpa [Nat.add_assoc] using run

/-- A unit-stride range has exactly `remaining` iterations. The premise proves
one actual source-body execution, with its continuation, preserving an invariant. -/
theorem rangeLoop (module : Module) (name : String) (body following : List Stmt)
    (stop : Int) (invariant : Int → ScalarEnv → Prop) (iterationCost : Nat)
    (iteration : ∀ i env, i < stop → invariant i env → ∀ stack,
      ∃ env', invariant (i + 1) env' ∧
        ReachesIn (step module)
          ⟨.block (body ++ [loopContinuation body
            (.rangeStepLoop name (i + 1) stop 1 body [])] ++ following)
            (env.set name (.int i)), stack⟩ iterationCost
          ⟨.block (.rangeStepLoop name (i + 1) stop 1 body [] :: following) env', stack⟩)
    (remaining : Nat) (start : Int) (env : ScalarEnv)
    (endpoint : stop = start + remaining) (valid : invariant start env) (stack : List Frame) :
    ∃ env', invariant stop env' ∧ ReachesIn (step module)
      ⟨.block (.rangeStepLoop name start stop 1 body [] :: following) env, stack⟩
      ((iterationCost + 1) * remaining + 1) ⟨.block following env', stack⟩ := by
  induction remaining generalizing start env with
  | zero =>
      have eq : stop = start := by simpa using endpoint
      refine ⟨env, eq ▸ valid, .next ?_ .refl⟩
      simp [step, rangeContinues, eq]
  | succ remaining ih =>
      have active : start < stop := by omega
      obtain ⟨env', valid', run⟩ := iteration start env active valid stack
      obtain ⟨final, validFinal, tail⟩ := ih (start + 1) env' (by omega) valid'
      refine ⟨final, validFinal, ?_⟩
      have first : step module
          ⟨.block (.rangeStepLoop name start stop 1 body [] :: following) env, stack⟩ =
          .next ⟨.block (body ++ [loopContinuation body
            (.rangeStepLoop name (start + 1) stop 1 body [])] ++ following)
            (env.set name (.int start)), stack⟩ := by
        simp [step, rangeContinues, active]
      have all := ReachesIn.next first (run.trans tail)
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all

end FormalSW.PyAst.Calls.Cost
