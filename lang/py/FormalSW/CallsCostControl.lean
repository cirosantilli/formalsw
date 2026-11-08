import lang.py.FormalSW.CallsCostLoops

/-! Bounded successful scalar block executions, including loop transfers. -/
namespace FormalSW.PyAst.Calls.Cost

/-- The same finite block trace works in every caller continuation. -/
def BlockWithin (module : Module) (env : ScalarEnv) (body : List Stmt) (bound : Nat) : Prop :=
  ∃ cost value, cost ≤ bound ∧ ∀ stack,
    ReachesIn (step module) ⟨.block body env, stack⟩ cost ⟨.value value, stack⟩

namespace BlockWithin

theorem mono (h : BlockWithin module env body small) (bound : small ≤ large) :
    BlockWithin module env body large := by
  obtain ⟨cost, value, bounded, run⟩ := h
  exact ⟨cost, value, Nat.le_trans bounded bound, run⟩

theorem return_value (evaluated : EvaluatesIn module env expression cost value) :
    BlockWithin module env (.return expression :: rest) (cost + 1) :=
  ⟨cost + 1, value, Nat.le_refl _, fun stack => .next rfl (evaluated stack)⟩

theorem assign (evaluated : EvaluatesIn module env expression cost value)
    (rest : BlockWithin module (env.set name value) following bound) :
    BlockWithin module env (.assign [.name name] expression :: following) (cost + 2 + bound) := by
  obtain ⟨tailCost, answer, bounded, tail⟩ := rest
  exact ⟨cost + 2 + tailCost, answer, by omega,
    fun stack => (Cost.assign evaluated name following stack).trans (tail stack)⟩

theorem branch (evaluated : EvaluatesIn module env condition cost (.bool flag))
    (rest : BlockWithin module env ((if flag then yes else no) ++ following) bound) :
    BlockWithin module env (.ifThen condition yes no :: following) (cost + 2 + bound) := by
  obtain ⟨tailCost, answer, bounded, tail⟩ := rest
  exact ⟨cost + 2 + tailCost, answer, by omega,
    fun stack => (Cost.branch evaluated yes no following stack).trans (tail stack)⟩

theorem range_step (active : rangeContinues next stop stride = true)
    (rest : BlockWithin module (env.set name (.int next))
      (body ++ [loopContinuation body (.rangeStepLoop name (next + stride) stop stride body otherwise)] ++ following) bound) :
    BlockWithin module env (.rangeStepLoop name next stop stride body otherwise :: following) (bound + 1) := by
  obtain ⟨cost, value, bounded, run⟩ := rest
  exact ⟨cost + 1, value, by omega, fun stack => .next (by simp [step, active]) (run stack)⟩

theorem range_done (inactive : rangeContinues next stop stride = false)
    (rest : BlockWithin module env (otherwise ++ following) bound) :
    BlockWithin module env (.rangeStepLoop name next stop stride body otherwise :: following) (bound + 1) := by
  obtain ⟨cost, value, bounded, run⟩ := rest
  exact ⟨cost + 1, value, by omega, fun stack => .next (by simp [step, inactive]) (run stack)⟩

theorem break_loop (target : loopTarget body = some (next, following))
    (rest : BlockWithin module env following bound) :
    BlockWithin module env (.breakLoop :: body) (bound + 1) := by
  obtain ⟨cost, value, bounded, run⟩ := rest
  exact ⟨cost + 1, value, by omega, fun stack => .next (by simp [step, target]) (run stack)⟩

theorem resume (rest : BlockWithin module env (next :: following) bound) :
    BlockWithin module env (.loopResume next :: following) (bound + 1) := by
  obtain ⟨cost, value, bounded, run⟩ := rest
  exact ⟨cost + 1, value, by omega, fun stack => .next rfl (run stack)⟩

end BlockWithin

namespace EvaluatesIn

inductive Arguments (module : Module) (env : ScalarEnv) : List Expr → Nat → List Constant → Prop where
  | nil : Arguments module env [] 0 []
  | cons : EvaluatesIn module env expression cost value →
      Arguments module env expressions tailCost values →
      Arguments module env (expression :: expressions) (cost + tailCost + 1) (value :: values)

theorem unary (evaluated : EvaluatesIn module env expression cost value)
    (result : scalarExpr (fun _ => none) (.unaryOp op (.constant value)) = some (.ok answer)) :
    EvaluatesIn module env (.unaryOp op expression) (cost + 2) answer := by
  intro stack
  exact .next rfl ((evaluated _).trans (.next (by simp [step, outcome, result]) .refl))

theorem conditional (condition : EvaluatesIn module env test ct (.bool flag))
    (branch : EvaluatesIn module env (if flag then yes else no) cb answer) :
    EvaluatesIn module env (.ifExp test yes no) (ct + cb + 2) answer := by
  intro stack
  have all := ReachesIn.next (step := step module)
    (state := ⟨.expr (.ifExp test yes no) env, stack⟩) rfl
    ((condition _).trans (.next rfl (branch stack)))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all

end EvaluatesIn

private def rangeState (name : String) (env : ScalarEnv) (done : List Constant)
    (expressions : List Expr) (body otherwise following : List Stmt) (stack : List Frame) : State :=
  match expressions with
  | [] => ⟨.startRange name done body otherwise following env, stack⟩
  | first :: rest => ⟨.expr first env, .rangeArguments name done rest body otherwise following env :: stack⟩

private theorem range_reach (h : EvaluatesIn.Arguments module env expressions cost values)
    (done : List Constant) (stack : List Frame) :
    ReachesIn (step module) (rangeState name env done expressions body otherwise following stack) cost
      ⟨.startRange name (done ++ values) body otherwise following env, stack⟩ := by
  induction h generalizing done with
  | nil => simp [rangeState]; exact .refl
  | @cons expression cost value expressions tailCost values head tail ih =>
      have run := (head (.rangeArguments name done expressions body otherwise following env :: stack)).trans
        (ReachesIn.next rfl (ih (done ++ [value])))
      simpa [rangeState, List.append_assoc, Nat.add_assoc] using run

theorem BlockWithin.for_range (arguments : EvaluatesIn.Arguments module env expressions cost values)
    (bounds : rangeBounds values = .ok (start, stop, stride))
    (rest : BlockWithin module env (.rangeStepLoop name start stop stride body otherwise :: following) bound) :
    BlockWithin module env (.forIn (.name name) (.call (.name "range") expressions) body otherwise :: following)
      (cost + 2 + bound) := by
  obtain ⟨tailCost, answer, bounded, run⟩ := rest
  refine ⟨cost + 2 + tailCost, answer, by omega, fun stack => ?_⟩
  have all := ReachesIn.next (step := step module)
    (state := ⟨.block (.forIn (.name name) (.call (.name "range") expressions) body otherwise :: following) env, stack⟩)
    rfl ((range_reach arguments [] stack).trans (.next (by simp [step, bounds]) (run stack)))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all

end FormalSW.PyAst.Calls.Cost
