import lang.py.FormalSW.CallsRuntimeCostLoops

/-! Compositional runtime costs for library calls, comparisons, assignments and guards.
Primitive charges follow the selected arithmetic policy. -/
namespace FormalSW.PyAst.Calls.Runtime

namespace EvaluatesIn

theorem library_pair (left : EvaluatesIn arithmetic module env a ca av)
    (right : EvaluatesIn arithmetic module env b cb bv)
    (absent : findFunctionIn module.body name = none)
    (result : libraryCall module name [av, bv] = some (.ok value))
    (measured : library arithmetic module name [av, bv] = some work) :
    EvaluatesIn arithmetic module env (.call (.name name) [a, b]) (ca + cb + work + 5) value := by
  intro stack
  have run := RuntimeCost.Reaches.next (charge := charge arithmetic module) (step := step module)
    (state := ⟨.expr (.call (.name name) [a, b]) env, stack⟩) rfl rfl
    ((left _).trans (.next rfl rfl ((right _).trans (.next rfl rfl
      (.next (amount := work + 1) (following := ⟨.value value, stack⟩) (by simp [step, absent, outcome, result]) (by simp [charge, absent, measured]) .refl)))))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem compare (left : EvaluatesIn arithmetic module env a ca av)
    (right : EvaluatesIn arithmetic module env b cb bv)
    (result : scalarCompare op av bv = some value) :
    EvaluatesIn arithmetic module env (.compare a [(op, b)]) (ca + cb + PrimitiveWork.comparison arithmetic av bv + 3) (.bool value) := by
  intro stack
  have run := RuntimeCost.Reaches.next (charge := charge arithmetic module) (step := step module)
    (state := ⟨.expr (.compare a [(op, b)]) env, stack⟩) rfl rfl
    ((left _).trans (.next rfl rfl ((right _).trans
      (.next (following := ⟨.value (.bool value), stack⟩) (by simp [step, outcome, result]) rfl .refl))))
  have eq : ca + cb + PrimitiveWork.comparison arithmetic av bv + 3 =
      1 + (ca + (1 + (cb + (PrimitiveWork.comparison arithmetic av bv + 1 + 0)))) := by omega
  rw [eq]
  exact run

end EvaluatesIn

/-- An assignment evaluates its right-hand side and installs its value. -/
theorem assign (evaluated : EvaluatesIn arithmetic module env expression cost value)
    (name : String) (following : List Stmt) (stack : List Frame) :
    RuntimeCost.Reaches (step module) (charge arithmetic module)
      ⟨.block (.assign [.name name] expression :: following) env, stack⟩ (cost + 2)
      ⟨.block following (env.set name value), stack⟩ := by
  have run := RuntimeCost.Reaches.next (charge := charge arithmetic module) (step := step module)
    (state := ⟨.block (.assign [.name name] expression :: following) env, stack⟩)
    rfl rfl ((evaluated _).trans (.next rfl rfl .refl))
  have eq : cost + 2 = 1 + (cost + (1 + 0)) := by omega
  rw [eq]
  exact run

theorem augAssign (evaluated : EvaluatesIn arithmetic module env (.binOp (.name name) op expression) cost value)
    (following : List Stmt) (stack : List Frame) :
    RuntimeCost.Reaches (step module) (charge arithmetic module)
      ⟨.block (.augAssign (.name name) op expression :: following) env, stack⟩ (cost + 2)
      ⟨.block following (env.set name value), stack⟩ := by
  have run := RuntimeCost.Reaches.next (charge := charge arithmetic module) (step := step module)
    (state := ⟨.block (.augAssign (.name name) op expression :: following) env, stack⟩)
    rfl rfl ((evaluated _).trans (.next rfl rfl .refl))
  have eq : cost + 2 = 1 + (cost + (1 + 0)) := by omega
  rw [eq]
  exact run

theorem unpackPair (left : EvaluatesIn arithmetic module env a ca av)
    (right : EvaluatesIn arithmetic module env b cb bv) (first second : String)
    (following : List Stmt) (stack : List Frame) :
    RuntimeCost.Reaches (step module) (charge arithmetic module)
      ⟨.block (.assign [.tuple [.name first, .name second]] (.tuple [a, b]) :: following) env, stack⟩
      (ca + cb + 8) ⟨.block following ((env.set first av).set second bv), stack⟩ := by
  have run := RuntimeCost.Reaches.next (charge := charge arithmetic module) (step := step module)
    (state := ⟨.block (.assign [.tuple [.name first, .name second]] (.tuple [a, b]) :: following) env, stack⟩)
    rfl rfl ((left _).trans (.next rfl rfl ((right _).trans (.next rfl rfl .refl))))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem branch (evaluated : EvaluatesIn arithmetic module env condition cost (.bool test))
    (yes no following : List Stmt) (stack : List Frame) :
    RuntimeCost.Reaches (step module) (charge arithmetic module) ⟨.block (.ifThen condition yes no :: following) env, stack⟩
      (cost + 2) ⟨.block ((if test then yes else no) ++ following) env, stack⟩ := by
  have run := RuntimeCost.Reaches.next (charge := charge arithmetic module) (step := step module)
    (state := ⟨.block (.ifThen condition yes no :: following) env, stack⟩)
    rfl rfl ((evaluated _).trans (.next rfl rfl .refl))
  have eq : cost + 2 = 1 + (cost + (1 + 0)) := by omega
  rw [eq]
  exact run

theorem whileTest (evaluated : EvaluatesIn arithmetic module env condition cost (.bool test))
    (body otherwise following : List Stmt) (stack : List Frame) :
    RuntimeCost.Reaches (step module) (charge arithmetic module) ⟨.block (.whileDo condition body otherwise :: following) env, stack⟩
      (cost + 2)
      ⟨.block ((if test then body ++ [loopContinuation body (.whileDo condition body otherwise)]
        else otherwise) ++ following) env, stack⟩ := by
  have run := RuntimeCost.Reaches.next (charge := charge arithmetic module) (step := step module)
    (state := ⟨.block (.whileDo condition body otherwise :: following) env, stack⟩)
    rfl rfl ((evaluated _).trans (.next rfl rfl .refl))
  have eq : cost + 2 = 1 + (cost + (1 + 0)) := by omega
  rw [eq]
  exact run


end FormalSW.PyAst.Calls.Runtime
