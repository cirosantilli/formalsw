import lang.py.FormalSW.HeapRuntimeCostControl

namespace FormalSW.PyAst.HeapCalls.Runtime
open PrimitiveWork

theorem sequenceComparison_ints (left right : List Int) (lengths : left.length = right.length) :
    sequenceComparison .word (left.map fun x => .scalar (.int x)) (right.map fun x => .scalar (.int x)) =
      some (3 * left.length + 1) := by
  induction left generalizing right with
  | nil => simp [sequenceComparison]
  | cons a rest ih =>
      cases right with
      | nil => simp at lengths
      | cons b tail =>
          have same : rest.length = tail.length := by simpa using lengths
          simp [sequenceComparison, elementComparison, PrimitiveWork.comparison, scalarSize, integer, ih tail same,
            Nat.mul_add, Nat.add_assoc]
          omega

namespace EvaluatesIn

theorem call_single (argument : EvaluatesIn arithmetic module env expression heap ca value middle)
    (callee : ReturnsIn arithmetic module name [value] middle cc answer finalHeap) :
    EvaluatesIn arithmetic module env (.call (.name name) [expression]) heap (ca + cc + 2) answer finalHeap := by
  intro anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.expr (.call (.name name) [expression]) env, stack, heap⟩ 1
      ⟨.expr expression env, .arguments (.call name) [] [] env :: stack, heap⟩ := advance rfl rfl rfl
  have next : Reaches arithmetic module anchors
      ⟨.value value, .arguments (.call name) [] [] env :: stack, middle⟩ 1
      ⟨.operation (.call name) [value], stack, middle⟩ := advance rfl rfl rfl
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    ((initial.trans (argument anchors _)).trans next).trans (callee anchors stack)

theorem maximum_pair (left : EvaluatesIn arithmetic module env a heap ca av middle)
    (right : EvaluatesIn arithmetic module env b middle cb bv finalHeap)
    (evaluated : primitive (.builtin .max) [av, bv] finalHeap = some (.ok answer, finalHeap))
    (priced : operation arithmetic finalHeap (.builtin .max) [av, bv] = some work) :
    EvaluatesIn arithmetic module env (.builtinCall .max [a, b]) heap (ca + cb + work + 5) answer finalHeap := by
  intro anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.expr (.builtinCall .max [a, b]) env, stack, heap⟩ 1
      ⟨.expr a env, .arguments (.builtin .max) [] [b] env :: stack, heap⟩ := advance rfl rfl rfl
  have next : Reaches arithmetic module anchors
      ⟨.value av, .arguments (.builtin .max) [] [b] env :: stack, middle⟩ 1
      ⟨.expr b env, .arguments (.builtin .max) [av] [] env :: stack, middle⟩ := advance rfl rfl rfl
  have arguments : Reaches arithmetic module anchors
      ⟨.value bv, .arguments (.builtin .max) [av] [] env :: stack, finalHeap⟩ 2
      ⟨.operation (.builtin .max) [av, bv], stack, finalHeap⟩ := advance rfl rfl rfl
  have last : Reaches arithmetic module anchors
      ⟨.operation (.builtin .max) [av, bv], stack, finalHeap⟩ (work + 1)
      ⟨.value answer, stack, finalHeap⟩ :=
    advance (by simp [step, result, run, evaluated]) (by simp [charge, priced]) rfl
  have total : 1 + ca + 1 + cb + 2 + (work + 1) = ca + cb + work + 5 := by omega
  simpa only [total] using
    ((((initial.trans (left anchors _)).trans next).trans (right anchors _)).trans arguments).trans last

theorem conditional (condition : EvaluatesIn arithmetic module env test heap ct (.scalar value) middle)
    (truth : Mutable.truth (.scalar value) middle = some (.ok flag, middle))
    (branch : EvaluatesIn arithmetic module env (if flag then yes else no) middle cb answer finalHeap) :
    EvaluatesIn arithmetic module env (.ifExp test yes no) heap (ct + cb + 2) answer finalHeap := by
  intro anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.expr (.ifExp test yes no) env, stack, heap⟩ 1
      ⟨.expr test env, .conditional yes no env :: stack, heap⟩ := advance rfl rfl rfl
  have next : Reaches arithmetic module anchors
      ⟨.value (.scalar value), .conditional yes no env :: stack, middle⟩ 1
      ⟨.expr (if flag then yes else no) env, stack, middle⟩ := advance (by simp [step, run, truth]) rfl rfl
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    ((initial.trans (condition anchors _)).trans next).trans (branch anchors stack)

end EvaluatesIn

namespace BlockContinuesIn

theorem branch (evaluated : EvaluatesIn arithmetic module env condition heap cc (.scalar value) middle)
    (test : Mutable.truth (.scalar value) middle = some (.ok flag, middle))
    (body : BlockContinuesIn arithmetic module env (if flag then yes else no) middle cb finalEnv finalHeap) :
    BlockContinuesIn arithmetic module env [.ifThen condition yes no] heap (cc + cb + 2) finalEnv finalHeap := by
  intro following anchors stack
  have initial : Reaches arithmetic module anchors
      ⟨.block ([.ifThen condition yes no] ++ following) env, stack, heap⟩ 1
      ⟨.expr condition env, .branch yes no following env :: stack, heap⟩ := advance rfl rfl rfl
  have next : Reaches arithmetic module anchors
      ⟨.value (.scalar value), .branch yes no following env :: stack, middle⟩ 1
      ⟨.block ((if flag then yes else no) ++ following) env, stack, middle⟩ :=
    advance (by simp [step, run, test]) rfl rfl
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    ((initial.trans (evaluated anchors _)).trans next).trans (body following anchors stack)

theorem range_step (continues : Calls.rangeContinues next stop stride = true)
    (rest : BlockContinuesIn .word module (setLocal env name (.scalar (.int next)))
      (body ++ [Calls.loopContinuation body (.rangeStepLoop name (next + stride) stop stride body otherwise)])
      heap budget finalEnv finalHeap) :
    BlockContinuesIn .word module env [.rangeStepLoop name next stop stride body otherwise]
      heap (budget + 4) finalEnv finalHeap := by
  intro following anchors stack
  have initial : Reaches .word module anchors
      ⟨.block ([.rangeStepLoop name next stop stride body otherwise] ++ following) env, stack, heap⟩ 4
      ⟨.block ((body ++ [Calls.loopContinuation body (.rangeStepLoop name (next + stride) stop stride body otherwise)]) ++ following)
        (setLocal env name (.scalar (.int next))), stack, heap⟩ :=
    advance (by simp [step, continues, List.append_assoc]) rfl rfl
  simpa only [Nat.add_comm] using initial.trans (rest following anchors stack)

theorem range_done (finished : Calls.rangeContinues next stop stride = false)
    (rest : BlockContinuesIn .word module env otherwise heap budget finalEnv finalHeap) :
    BlockContinuesIn .word module env [.rangeStepLoop name next stop stride body otherwise]
      heap (budget + 4) finalEnv finalHeap := by
  intro following anchors stack
  have initial : Reaches .word module anchors
      ⟨.block ([.rangeStepLoop name next stop stride body otherwise] ++ following) env, stack, heap⟩ 4
      ⟨.block (otherwise ++ following) env, stack, heap⟩ := advance (by simp [step, finished]) rfl rfl
  simpa only [Nat.add_comm] using initial.trans (rest following anchors stack)

/-- A one-bound range evaluates its endpoint once before entering the loop. -/
theorem for_range_bound
    (bound : EvaluatesIn .word module env expression heap ce (.scalar (.int stop)) middle)
    (body : BlockContinuesIn .word module env [.rangeStepLoop name 0 stop 1 loop otherwise]
      middle cb finalEnv finalHeap) :
    BlockContinuesIn .word module env [.forIn (.name name) (.call (.name "range") [expression]) loop otherwise]
      heap (ce+cb+4) finalEnv finalHeap := by
  intro following anchors stack
  have initial : Reaches .word module anchors
      ⟨.block ([.forIn (.name name) (.call (.name "range") [expression]) loop otherwise] ++ following) env, stack, heap⟩ 1
      ⟨.expr expression env, .rangeArguments name [] [] loop otherwise following env :: stack, heap⟩ :=
    advance rfl rfl rfl
  have argument : Reaches .word module anchors
      ⟨.value (.scalar (.int stop)), .rangeArguments name [] [] loop otherwise following env :: stack, middle⟩ 1
      ⟨.startRange name [.scalar (.int stop)] loop otherwise following env, stack, middle⟩ := advance rfl rfl rfl
  have enter : Reaches .word module anchors
      ⟨.startRange name [.scalar (.int stop)] loop otherwise following env, stack, middle⟩ 2
      ⟨.block ([.rangeStepLoop name 0 stop 1 loop otherwise] ++ following) env, stack, middle⟩ := advance rfl rfl rfl
  exact ((((initial.trans (bound anchors _)).trans argument).trans enter).trans (body following anchors stack)).mono (by omega)

theorem for_range_pair (left : EvaluatesIn .word module env a heap ca (.scalar (.int start)) middle)
    (right : EvaluatesIn .word module env b middle cb (.scalar (.int stop)) afterBounds)
    (body : BlockContinuesIn .word module env [.rangeStepLoop name start stop 1 loop otherwise]
      afterBounds cost finalEnv finalHeap) :
    BlockContinuesIn .word module env [.forIn (.name name) (.call (.name "range") [a, b]) loop otherwise]
      heap (ca + cb + cost + 7) finalEnv finalHeap := by
  intro following anchors stack
  have initial : Reaches .word module anchors
      ⟨.block ([.forIn (.name name) (.call (.name "range") [a, b]) loop otherwise] ++ following) env, stack, heap⟩ 1
      ⟨.expr a env, .rangeArguments name [] [b] loop otherwise following env :: stack, heap⟩ := advance rfl rfl rfl
  have next : Reaches .word module anchors
      ⟨.value (.scalar (.int start)), .rangeArguments name [] [b] loop otherwise following env :: stack, middle⟩ 1
      ⟨.expr b env, .rangeArguments name [.scalar (.int start)] [] loop otherwise following env :: stack, middle⟩ :=
    advance rfl rfl rfl
  have arguments : Reaches .word module anchors
      ⟨.value (.scalar (.int stop)), .rangeArguments name [.scalar (.int start)] [] loop otherwise following env :: stack, afterBounds⟩ 2
      ⟨.startRange name [.scalar (.int start), .scalar (.int stop)] loop otherwise following env, stack, afterBounds⟩ :=
    advance rfl rfl rfl
  have enter : Reaches .word module anchors
      ⟨.startRange name [.scalar (.int start), .scalar (.int stop)] loop otherwise following env, stack, afterBounds⟩ 3
      ⟨.block ([.rangeStepLoop name start stop 1 loop otherwise] ++ following) env, stack, afterBounds⟩ :=
    advance rfl rfl rfl
  have total : 1 + ca + 1 + cb + 2 + 3 + cost = ca + cb + cost + 7 := by omega
  simpa only [total] using
    (((((initial.trans (left anchors _)).trans next).trans (right anchors _)).trans arguments).trans enter).trans
      (body following anchors stack)

end BlockContinuesIn
end FormalSW.PyAst.HeapCalls.Runtime
