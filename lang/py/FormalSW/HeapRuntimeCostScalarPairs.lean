import lang.py.FormalSW.HeapRuntimeCostComprehensions

namespace FormalSW.PyAst.HeapCalls.Runtime

/-- `divmod` pays for division, remainder and allocating the returned pair. -/
theorem EvaluatesIn.divmod_ints
    (left : EvaluatesIn .word module env a heap ca (.scalar (.int n)) middle)
    (right : EvaluatesIn .word module env b middle cb (.scalar (.int d)) afterRight)
    (nonzero : d ≠ 0) :
    EvaluatesIn .word module env (.builtinCall .divmod [a, b]) heap (ca+cb+10)
      (.ref afterRight.length)
      (afterRight ++ [.tuple [.scalar (.int (n.fdiv d)), .scalar (.int (n-d*n.fdiv d))]]) := by
  intro anchors stack
  have first : Reaches .word module anchors
      ⟨.expr (.builtinCall .divmod [a, b]) env, stack, heap⟩ 1
      ⟨.expr a env, .arguments (.builtin .divmod) [] [b] env :: stack, heap⟩ := advance rfl rfl rfl
  have next : Reaches .word module anchors
      ⟨.value (.scalar (.int n)), .arguments (.builtin .divmod) [] [b] env :: stack, middle⟩ 1
      ⟨.expr b env, .arguments (.builtin .divmod) [.scalar (.int n)] [] env :: stack, middle⟩ :=
    advance rfl rfl rfl
  have ready : Reaches .word module anchors
      ⟨.value (.scalar (.int d)), .arguments (.builtin .divmod) [.scalar (.int n)] [] env :: stack, afterRight⟩ 2
      ⟨.operation (.builtin .divmod) [.scalar (.int n), .scalar (.int d)], stack, afterRight⟩ :=
    advance rfl rfl rfl
  have divided : Reaches .word module anchors
      ⟨.operation (.builtin .divmod) [.scalar (.int n), .scalar (.int d)], stack, afterRight⟩ 6
      ⟨.value (.ref afterRight.length), stack,
        afterRight ++ [.tuple [.scalar (.int (n.fdiv d)), .scalar (.int (n-d*n.fdiv d))]]⟩ := by
    apply RuntimeCost.Amortized.Reaches.next (amount := 6)
    · simp [step, result, run, primitive, Mutable.divmod_ints n d nonzero]
    · rfl
    · simp [potential, heapPotential, objectPotential]
  exact (((((first.trans (left anchors _)).trans next).trans (right anchors _)).trans ready).trans divided).mono (by omega)

end FormalSW.PyAst.HeapCalls.Runtime
