import lang.py.FormalSW.MemoCalls

/-! Compositional proof rules for scalar execution with a shared memoization cache. -/
namespace FormalSW.PyAst.MemoCalls

theorem Runs.next (plain : transparent memoized state)
    (transition : Calls.step module state = .next following)
    (rest : Runs module memoized spec following final) : Runs module memoized spec state final :=
  (Runs.raw plain transition).trans rest

namespace Evaluates

theorem constant : Evaluates module memoized spec env (.constant value) value :=
  fun _ => Runs.raw (by trivial) rfl

theorem lookup (found : env name = some value) :
    Evaluates module memoized spec env (.name name) value :=
  fun _ => Runs.raw (by trivial) (by simp [Calls.step, Calls.outcome, found])

theorem binary (left : Evaluates module memoized spec env a av)
    (right : Evaluates module memoized spec env b bv)
    (result : scalarBinary op av bv = some (.ok value)) :
    Evaluates module memoized spec env (.binOp a op b) value := by
  intro stack
  apply Runs.next (by trivial) rfl
  apply Runs.trans (left _)
  apply Runs.next (by trivial) rfl
  apply Runs.trans (right _)
  exact Runs.raw (by trivial) (by simp [Calls.step, Calls.outcome, result])

theorem compare (left : Evaluates module memoized spec env a av)
    (right : Evaluates module memoized spec env b bv)
    (result : scalarCompare op av bv = some answer) :
    Evaluates module memoized spec env (.compare a [(op, b)]) (.bool answer) := by
  intro stack
  apply Runs.next (by trivial) rfl
  apply Runs.trans (left _)
  apply Runs.next (by trivial) rfl
  apply Runs.trans (right _)
  exact Runs.raw (by trivial) (by simp [Calls.step, Calls.outcome, result])

theorem conditional (condition : Evaluates module memoized spec env test c)
    (branch : Evaluates module memoized spec env (if scalarTruth c then yes else no) value) :
    Evaluates module memoized spec env (.ifExp test yes no) value := by
  intro stack
  apply Runs.next (by trivial) rfl
  apply Runs.trans (condition _)
  exact Runs.next (by trivial) rfl (branch _)

inductive Arguments (module : Module) (memoized : List String) (spec : Specification)
    (env : ScalarEnv) : List Expr → List Constant → Prop where
  | nil : Arguments module memoized spec env [] []
  | cons : Evaluates module memoized spec env expression value →
      Arguments module memoized spec env expressions values →
      Arguments module memoized spec env (expression :: expressions) (value :: values)

private theorem arguments_reach (arguments : Arguments module memoized spec env expressions values)
    (done : List Constant) (stack : List Calls.Frame) :
    Runs module memoized spec
      (match expressions with
      | [] => ⟨.invoke name done, stack⟩
      | first :: rest => ⟨.expr first env, .arguments name done rest env :: stack⟩)
      ⟨.invoke name (done ++ values), stack⟩ := by
  induction arguments generalizing done with
  | nil => simpa using Runs.refl
  | @cons expression value expressions values head tail ih =>
      apply (head _).trans
      cases expressions with
      | nil =>
          cases tail
          exact Runs.raw (by trivial) rfl
      | cons first rest =>
          apply Runs.next (following := ⟨.expr first env,
            .arguments name (done ++ [value]) rest env :: stack⟩) (by trivial) rfl
          simpa [List.append_assoc] using ih (done ++ [value])

theorem call (arguments : Arguments module memoized spec env expressions values)
    (result : ReturnsValue module memoized spec name values value) :
    Evaluates module memoized spec env (.call (.name name) expressions) value := by
  intro stack
  cases expressions with
  | nil =>
      cases arguments
      exact Runs.next (by trivial) rfl (result stack)
  | cons first rest =>
      apply Runs.next (by trivial) rfl
      exact (arguments_reach arguments [] stack).trans (result stack)

theorem condition_int_compare
    (holds : Condition module memoized env (.compare (.name name) [(op, .constant (.int bound))]))
    (found : env name = some (.int input)) : evalCmpOp op input bound = true := by
  have run : Evaluates module memoized (fun _ _ => True) env
      (.compare (.name name) [(op, .constant (.int bound))]) (.bool (evalCmpOp op input bound)) :=
    compare (Evaluates.lookup found) constant rfl
  simpa using run.condition_iff.mp holds

end Evaluates


def ExtremumReturns (module : Module) (memoized : List String) (spec : Specification)
    (range : Calls.RangeExtremum) (current : Int) (best : Option (Int × Constant)) (result : Int) : Prop :=
  ∀ stack, Runs module memoized spec ⟨.extremumLoop range current best, stack⟩
    ⟨.value (.int result), stack⟩

namespace ExtremumReturns

theorem done (finished : Calls.rangeContinues current range.stop range.stride = false) :
    ExtremumReturns module memoized spec range current (some (winner, score)) winner :=
  fun _ => Runs.raw (by trivial) (by simp [Calls.step, finished])

theorem next (continues : Calls.rangeContinues current range.stop range.stride = true)
    (key : ReturnsValue module memoized spec range.key [.int current] score)
    (selected : range.choose current score best = .ok updated)
    (rest : ExtremumReturns module memoized spec range (current + range.stride) (some updated) result) :
    ExtremumReturns module memoized spec range current best result := by
  intro stack
  apply Runs.next (following := ⟨.invoke range.key [.int current],
    .extremumKey range current best :: stack⟩) (by trivial) (by simp [Calls.step, continues])
  apply Runs.trans (key _)
  exact Runs.next (by trivial) (by simp [Calls.step, selected]) (rest stack)

end ExtremumReturns

private def extremumState (maximum : Bool) (key : String) (env : ScalarEnv)
    (done : List Constant) (expressions : List Expr) (stack : List Calls.Frame) : Calls.State :=
  match expressions with
  | [] => ⟨.startExtremum maximum key done, stack⟩
  | first :: rest => ⟨.expr first env, .extremumArguments maximum key done rest env :: stack⟩

private theorem extremum_reach
    (h : Evaluates.Arguments module memoized spec env expressions values) (done : List Constant)
    (stack : List Calls.Frame) :
    Runs module memoized spec (extremumState maximum key env done expressions stack)
      ⟨.startExtremum maximum key (done ++ values), stack⟩ := by
  induction h generalizing done with
  | nil => simpa [extremumState] using Runs.refl
  | @cons expression value expressions values head tail ih =>
      apply Runs.trans (head _)
      apply Runs.next (by trivial) rfl
      simpa [List.append_assoc] using ih (done ++ [value])

theorem Evaluates.extremum_range (arguments : Evaluates.Arguments module memoized spec env expressions values)
    (bounds : Calls.rangeBounds values = .ok (start, stop, stride))
    (rest : ExtremumReturns module memoized spec ⟨maximum, key, stop, stride⟩ start none result) :
    Evaluates module memoized spec env (.extremumRange maximum expressions key) (.int result) := by
  intro stack
  apply Runs.next (following := extremumState maximum key env [] expressions stack) (by trivial) rfl
  apply Runs.trans (extremum_reach arguments [] stack)
  exact Runs.next (by trivial) (by simp [Calls.step, bounds]) (rest stack)

namespace BlockReturns

theorem return_value (run : Evaluates module memoized spec env expression value) :
    BlockReturns module memoized spec env (.return expression :: rest) value :=
  fun stack => Runs.next (by trivial) rfl (run stack)

theorem branch (test : Evaluates module memoized spec env condition value)
    (rest : BlockReturns module memoized spec env ((if scalarTruth value then yes else no) ++ body) result) :
    BlockReturns module memoized spec env (.ifThen condition yes no :: body) result := by
  intro stack
  apply Runs.next (by trivial) rfl
  apply Runs.trans (test _)
  exact Runs.next (by trivial) rfl (rest stack)

theorem assign (run : Evaluates module memoized spec env expression value)
    (rest : BlockReturns module memoized spec (env.set name value) body result) :
    BlockReturns module memoized spec env (.assign [.name name] expression :: body) result := by
  intro stack
  apply Runs.next (by trivial) rfl
  apply Runs.trans (run _)
  exact Runs.next (by trivial) rfl (rest stack)

end BlockReturns
end FormalSW.PyAst.MemoCalls
