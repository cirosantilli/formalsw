import lang.py.FormalSW.CallsRuntimeCostControl

namespace FormalSW.PyAst.Calls.Runtime

/-- A charged function call in any caller continuation. -/
def ReturnsIn (arithmetic : PrimitiveWork.Arithmetic) (module : Module)
    (name : String) (values : List Constant) (cost : Nat) (value : Constant) : Prop :=
  ∀ stack, RuntimeCost.Reaches (step module) (charge arithmetic module)
    ⟨.invoke name values, stack⟩ cost ⟨.value value, stack⟩

theorem ReturnsIn.timeBound (run : ReturnsIn arithmetic module name values cost value) :
    TimeBound arithmetic module name values (cost + 1) :=
  ⟨cost + 1, .ok value, (run []).finishes (.done rfl rfl), Nat.le_refl _⟩

namespace EvaluatesIn

theorem call_single (argument : EvaluatesIn arithmetic module env expression ca input)
    (callee : ReturnsIn arithmetic module name [input] cc value) :
    EvaluatesIn arithmetic module env (.call (.name name) [expression]) (ca + cc + 2) value := by
  intro stack
  have run := RuntimeCost.Reaches.next (charge := charge arithmetic module) (step := step module)
    (state := ⟨.expr (.call (.name name) [expression]) env, stack⟩) rfl rfl
    ((argument _).trans (.next rfl rfl (callee stack)))
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem conditional
    (test : EvaluatesIn arithmetic module env condition ct (.bool flag))
    (selected : EvaluatesIn arithmetic module env (if flag then yes else no) cb value) :
    EvaluatesIn arithmetic module env (.ifExp condition yes no) (ct + cb + 2) value := by
  intro stack
  have run := RuntimeCost.Reaches.next (charge := charge arithmetic module) (step := step module)
    (state := ⟨.expr (.ifExp condition yes no) env, stack⟩) rfl rfl
    ((test _).trans (.next rfl rfl (selected stack)))
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem call_pair (left : EvaluatesIn arithmetic module env a ca av)
    (right : EvaluatesIn arithmetic module env b cb bv)
    (callee : ReturnsIn arithmetic module name [av, bv] cc value) :
    EvaluatesIn arithmetic module env (.call (.name name) [a, b])
      (ca + cb + cc + 4) value := by
  intro stack
  have run := RuntimeCost.Reaches.next (charge := charge arithmetic module) (step := step module)
    (state := ⟨.expr (.call (.name name) [a, b]) env, stack⟩) rfl rfl
    ((left _).trans (.next rfl rfl ((right _).trans (.next rfl rfl (callee stack)))))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem builtin_pair (left : EvaluatesIn arithmetic module env a ca av)
    (right : EvaluatesIn arithmetic module env b cb bv)
    (result : Primitive.apply (.builtin builtin) [av, bv] = some (.ok value))
    (measured : primitive arithmetic (.builtin builtin) [av, bv] = some work) :
    EvaluatesIn arithmetic module env (.builtinCall builtin [a, b])
      (ca + cb + work + 5) value := by
  intro stack
  have run := RuntimeCost.Reaches.next (charge := charge arithmetic module) (step := step module)
    (state := ⟨.expr (.builtinCall builtin [a, b]) env, stack⟩) rfl rfl
    ((left _).trans (.next rfl rfl ((right _).trans (.next rfl rfl
      (.next (amount := work + 1) (following := ⟨.value value, stack⟩)
        (by change step module ⟨.primitive (.builtin builtin) [av, bv], stack⟩ = _; simp [step, outcome, result]) (by change (primitive arithmetic (.builtin builtin) [av, bv]).map (· + 1) = _; rw [measured]; rfl) .refl)))))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem boolean_pair (op : BoolOp) (left : EvaluatesIn arithmetic module env a ca av)
    (right : EvaluatesIn arithmetic module env b cb bv)
    (continues : (match op with | .and => !scalarTruth av | .or => scalarTruth av) = false) :
    EvaluatesIn arithmetic module env (.boolOp op [a, b]) (ca + cb + 3) bv := by
  intro stack
  have select : step module ⟨.value av, .boolean op [b] env :: stack⟩ =
      .next ⟨.expr b env, .boolean op [] env :: stack⟩ := by
    cases op <;> dsimp only [step] at continues ⊢ <;> rw [continues] <;> rfl
  have finish : step module ⟨.value bv, .boolean op [] env :: stack⟩ =
      .next ⟨.value bv, stack⟩ := by
    dsimp only [step]
    simp only [ite_self]
    rfl
  have run := RuntimeCost.Reaches.next (charge := charge arithmetic module) (step := step module)
    (state := ⟨.expr (.boolOp op [a, b]) env, stack⟩) rfl rfl
    ((left _).trans (.next select rfl ((right _).trans (.next finish rfl .refl))))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

end EvaluatesIn
end FormalSW.PyAst.Calls.Runtime
