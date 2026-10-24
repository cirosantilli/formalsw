import lang.py.FormalSW.Calls

/-! Composable source proofs for short-circuiting scalar comparison chains. -/
namespace FormalSW.PyAst.Calls.Evaluates

def Compares (module : Module) (env : ScalarEnv) (left : Constant) (op : CmpOp) (right : Expr)
    (rest : List (CmpOp × Expr)) (answer : Bool) : Prop :=
  ∀ stack, Reaches module ⟨.expr right env, .chainRight op left rest env :: stack⟩
    ⟨.value (.bool answer), stack⟩

namespace Compares

theorem last (evaluated : Evaluates module env right value)
    (compared : scalarCompare op left value = some answer) :
    Compares module env left op right [] answer := by
  intro stack
  apply (evaluated _).trans
  exact .next (by cases answer <;> simp [step, compared]) .refl

theorem stop (evaluated : Evaluates module env right value)
    (compared : scalarCompare op left value = some false) :
    Compares module env left op right rest false := by
  intro stack
  exact (evaluated _).trans (.next (by simp [step, compared]) .refl)

theorem next (evaluated : Evaluates module env right value)
    (compared : scalarCompare op left value = some true)
    (following : Compares module env value nextOp nextRight rest answer) :
    Compares module env left op right ((nextOp, nextRight) :: rest) answer := by
  intro stack
  exact (evaluated _).trans (.next (by simp [step, compared]) (following stack))

end Compares

theorem chain (left : Evaluates module env expression value)
    (following : Compares module env value op right (next :: rest) answer) :
    Evaluates module env (.compare expression ((op, right) :: next :: rest)) (.bool answer) := by
  intro stack
  exact .next rfl ((left _).trans (.next rfl (following stack)))

end FormalSW.PyAst.Calls.Evaluates
