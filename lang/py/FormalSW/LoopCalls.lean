import lang.py.FormalSW.HeapCalls

/-! Loop transfers inside blocks with an arbitrary following continuation. -/
namespace FormalSW.PyAst

theorem Calls.loopTarget_append (target : Calls.loopTarget body = some (next, rest))
    (following : List Stmt) :
    Calls.loopTarget (body ++ following) = some (next, rest ++ following) := by
  induction body with
  | nil => simp [Calls.loopTarget] at target
  | cons head tail ih =>
      cases head <;> simp_all [Calls.loopTarget]

namespace HeapCalls.BlockContinues

/-- Keep the loop boundary in scope when a selected branch transfers control. -/
theorem branch_next
    (evaluated : Evaluates (globals := globals) module env condition heap value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (executed : BlockContinues (globals := globals) module env
      ((if flag then yes else no) ++ rest) middle finalEnv finalHeap) :
    BlockContinues (globals := globals) module env (.ifThen condition yes no :: rest) heap finalEnv finalHeap := by
  intro following anchors stack
  apply Reaches.next rfl
  apply (evaluated anchors _).trans
  refine Reaches.next ?_ (executed following anchors stack)
  simp [step, run, truth, List.append_assoc]

theorem break_loop (target : Calls.loopTarget body = some (next, rest))
    (executed : BlockContinues (globals := globals) module env rest heap finalEnv finalHeap) :
    BlockContinues (globals := globals) module env (.breakLoop :: body) heap finalEnv finalHeap := by
  intro following anchors stack
  exact .next (by simp [step, Calls.loopTarget_append target following]) (executed following anchors stack)

theorem continue_loop (target : Calls.loopTarget body = some (next, rest))
    (executed : BlockContinues (globals := globals) module env (next :: rest) heap finalEnv finalHeap) :
    BlockContinues (globals := globals) module env (.continueLoop :: body) heap finalEnv finalHeap := by
  intro following anchors stack
  exact .next (by simp [step, Calls.loopTarget_append target following]) (executed following anchors stack)

end HeapCalls.BlockContinues
end FormalSW.PyAst
