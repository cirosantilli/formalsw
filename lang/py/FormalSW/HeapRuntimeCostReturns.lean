import lang.py.FormalSW.HeapRuntimeCostRanges

/-! Runtime rules for early returns from range loops. -/
namespace FormalSW.PyAst.HeapCalls.Runtime.BlockReturnsIn

theorem augAssign (lookup : env name = some (.scalar left))
    (evaluated : EvaluatesIn arithmetic module env expression heap ca (.scalar right) middle)
    (operation : inplace op (.scalar left) (.scalar right) middle = some (.ok value, middle))
    (priced : PrimitiveWork.binary arithmetic op left right = some work)
    (rest : BlockReturnsIn arithmetic module (setLocal env name value) following middle cb answer finalHeap) :
    BlockReturnsIn arithmetic module env (.augAssign (.name name) op expression :: following) heap
      (ca + work + 5 + cb) answer finalHeap :=
  (BlockContinuesIn.augAssign lookup evaluated operation priced).returns rest

theorem range_step (continues : Calls.rangeContinues next stop stride = true)
    (rest : BlockReturnsIn .word module (setLocal env name (.scalar (.int next)))
      ((body ++ [Calls.loopContinuation body (.rangeStepLoop name (next + stride) stop stride body otherwise)]) ++ following)
      heap budget answer finalHeap) :
    BlockReturnsIn .word module env (.rangeStepLoop name next stop stride body otherwise :: following)
      heap (budget + 4) answer finalHeap := by
  intro anchors stack
  have initial : Reaches .word module anchors
      ⟨.block (.rangeStepLoop name next stop stride body otherwise :: following) env, stack, heap⟩ 4
      ⟨.block ((body ++ [Calls.loopContinuation body (.rangeStepLoop name (next + stride) stop stride body otherwise)]) ++ following)
        (setLocal env name (.scalar (.int next))), stack, heap⟩ :=
    advance (by simp [step, continues, List.append_assoc]) rfl rfl
  exact (initial.trans (rest anchors stack)).mono (by omega)

theorem for_range_pair (left : EvaluatesIn .word module env a heap ca (.scalar (.int start)) middle)
    (right : EvaluatesIn .word module env b middle cb (.scalar (.int stop)) afterBounds)
    (body : BlockReturnsIn .word module env (.rangeStepLoop name start stop 1 loop otherwise :: following)
      afterBounds cost answer finalHeap) :
    BlockReturnsIn .word module env (.forIn (.name name) (.call (.name "range") [a, b]) loop otherwise :: following)
      heap (ca + cb + cost + 7) answer finalHeap := by
  intro anchors stack
  have initial : Reaches .word module anchors
      ⟨.block (.forIn (.name name) (.call (.name "range") [a, b]) loop otherwise :: following) env, stack, heap⟩ 1
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
      ⟨.block (.rangeStepLoop name start stop 1 loop otherwise :: following) env, stack, afterBounds⟩ :=
    advance rfl rfl rfl
  exact ((((((initial.trans (left anchors _)).trans next).trans (right anchors _)).trans arguments).trans enter).trans
      (body anchors stack)).mono (by omega)

end FormalSW.PyAst.HeapCalls.Runtime.BlockReturnsIn
