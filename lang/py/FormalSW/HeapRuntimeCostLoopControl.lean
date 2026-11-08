import lang.py.FormalSW.HeapRuntimeCostSequences

namespace FormalSW.PyAst.HeapCalls.Runtime

theorem ReturnsIn.mono (run : ReturnsIn arithmetic module name values heap small value finalHeap)
    (larger : small ≤ large) : ReturnsIn arithmetic module name values heap large value finalHeap :=
  fun anchors stack => (run anchors stack).mono larger

theorem BlockContinuesIn.loop_resume
    (rest : BlockContinuesIn arithmetic module env [next] heap budget finalEnv finalHeap) :
    BlockContinuesIn arithmetic module env [.loopResume next] heap (budget + 1) finalEnv finalHeap := by
  intro following anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.block ([.loopResume next] ++ following) env, stack, heap⟩ 1
      ⟨.block ([next] ++ following) env, stack, heap⟩ := advance rfl rfl rfl
  exact (first.trans (rest following anchors stack)).mono (by omega)

theorem BlockContinuesIn.continue_over
    (target : ∀ following, Calls.loopTarget (body ++ following) = some (next, following))
    (rest : BlockContinuesIn arithmetic module env [next] heap budget finalEnv finalHeap) :
    BlockContinuesIn arithmetic module env (.continueLoop :: body) heap (budget + 1) finalEnv finalHeap := by
  intro following anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.block ((.continueLoop :: body) ++ following) env, stack, heap⟩ 1
      ⟨.block ([next] ++ following) env, stack, heap⟩ := advance (by simp [step, target]) rfl rfl
  exact (first.trans (rest following anchors stack)).mono (by omega)

theorem BlockContinuesIn.branch_tail
    (evaluated : EvaluatesIn arithmetic module env condition heap cc (.scalar value) middle)
    (test : Mutable.truth (.scalar value) middle = some (.ok flag, middle))
    (rest : BlockContinuesIn arithmetic module env ((if flag then yes else no) ++ body)
      middle cb finalEnv finalHeap) :
    BlockContinuesIn arithmetic module env (.ifThen condition yes no :: body) heap
      (cc + cb + 2) finalEnv finalHeap := by
  intro following anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.block ((.ifThen condition yes no :: body) ++ following) env, stack, heap⟩ 1
      ⟨.expr condition env, .branch yes no (body ++ following) env :: stack, heap⟩ := advance rfl rfl rfl
  have chosen : Reaches arithmetic module anchors
      ⟨.value (.scalar value), .branch yes no (body ++ following) env :: stack, middle⟩ 1
      ⟨.block (((if flag then yes else no) ++ body) ++ following) env, stack, middle⟩ :=
    advance (by simp [step, run, test, List.append_assoc]) rfl rfl
  exact (((first.trans (evaluated anchors _)).trans chosen).trans (rest following anchors stack)).mono (by omega)

end FormalSW.PyAst.HeapCalls.Runtime

namespace FormalSW.PyAst.HeapCalls.Runtime.BlockReturnsIn

theorem loop_resume (rest : BlockReturnsIn arithmetic module env (next :: following) heap budget answer finalHeap) :
    BlockReturnsIn arithmetic module env (.loopResume next :: following) heap (budget + 1) answer finalHeap := by
  intro anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.block (.loopResume next :: following) env, stack, heap⟩ 1
      ⟨.block (next :: following) env, stack, heap⟩ := advance rfl rfl rfl
  simpa only [Nat.add_comm] using first.trans (rest anchors stack)

theorem break_loop (target : Calls.loopTarget body = some (next, following))
    (rest : BlockReturnsIn arithmetic module env following heap budget answer finalHeap) :
    BlockReturnsIn arithmetic module env (.breakLoop :: body) heap (budget + 1) answer finalHeap := by
  intro anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.block (.breakLoop :: body) env, stack, heap⟩ 1
      ⟨.block following env, stack, heap⟩ := advance (by simp [step, target]) rfl rfl
  simpa only [Nat.add_comm] using first.trans (rest anchors stack)

end FormalSW.PyAst.HeapCalls.Runtime.BlockReturnsIn
