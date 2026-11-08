import lang.py.FormalSW.CallsRuntimeCostScaled

/-! Runtime bounds for complete scalar blocks, including early loop exits.
The common operation budget bounds actual tariffs, including range setup and
argument-frame work; it never supplies a tariff for an unsupported operation. -/
namespace FormalSW.PyAst.Calls.Runtime.Scaled

def BlockWithin (arithmetic : PrimitiveWork.Arithmetic) (module : Module) (unit : Nat)
    (env : ScalarEnv) (body : List Stmt) (bound : Nat) : Prop :=
  ∃ cost value, cost ≤ unit*bound ∧ ∀ stack,
    RuntimeCost.Reaches (step module) (charge arithmetic module)
      ⟨.block body env, stack⟩ cost ⟨.value value, stack⟩

namespace BlockWithin

theorem mono (h : BlockWithin arithmetic module unit env body small) (bound : small ≤ large) :
    BlockWithin arithmetic module unit env body large := by
  obtain ⟨cost, value, bounded, run⟩ := h
  exact ⟨cost, value, Nat.le_trans bounded (Nat.mul_le_mul_left unit bound), run⟩

theorem return_value (positive : 1 ≤ unit)
    (evaluated : EvaluatesIn arithmetic module unit env expression budget value) :
    BlockWithin arithmetic module unit env (.return expression :: rest) (budget+1) := by
  obtain ⟨cost, bound, run⟩ := evaluated
  refine ⟨1+cost, value, ?_, fun stack => .next rfl rfl (run stack)⟩
  simp only [Nat.mul_add, Nat.mul_one]
  omega

theorem assign (positive : 1 ≤ unit)
    (evaluated : EvaluatesIn arithmetic module unit env expression budget value)
    (rest : BlockWithin arithmetic module unit (env.set name value) following bound) :
    BlockWithin arithmetic module unit env (.assign [.name name] expression :: following)
      (budget+2+bound) := by
  obtain ⟨cost, headBound, head⟩ := evaluated
  obtain ⟨tailCost, answer, tailBound, tail⟩ := rest
  refine ⟨cost+2+tailCost, answer, ?_, fun stack => (Runtime.assign head name following stack).trans (tail stack)⟩
  simp only [Nat.mul_add]
  omega

theorem branch (positive : 1 ≤ unit)
    (evaluated : EvaluatesIn arithmetic module unit env condition budget (.bool flag))
    (rest : BlockWithin arithmetic module unit env ((if flag then yes else no) ++ following) bound) :
    BlockWithin arithmetic module unit env (.ifThen condition yes no :: following) (budget+2+bound) := by
  obtain ⟨cost, headBound, head⟩ := evaluated
  obtain ⟨tailCost, answer, tailBound, tail⟩ := rest
  refine ⟨cost+2+tailCost, answer, ?_, fun stack => (Runtime.branch head yes no following stack).trans (tail stack)⟩
  simp only [Nat.mul_add]
  omega

theorem range_step (active : rangeContinues next stop stride = true)
    (priced : rangeWork arithmetic next stop stride ≤ unit)
    (rest : BlockWithin arithmetic module unit (env.set name (.int next))
      (body ++ [loopContinuation body (.rangeStepLoop name (next+stride) stop stride body otherwise)] ++ following) bound) :
    BlockWithin arithmetic module unit env (.rangeStepLoop name next stop stride body otherwise :: following) (bound+1) := by
  obtain ⟨cost, value, bounded, run⟩ := rest
  refine ⟨rangeWork arithmetic next stop stride+cost, value, ?_, fun stack => ?_⟩
  · simp only [Nat.mul_add, Nat.mul_one]; omega
  · exact .next (by simp [step, active]) rfl (run stack)

theorem range_done (inactive : rangeContinues next stop stride = false)
    (priced : rangeWork arithmetic next stop stride ≤ unit)
    (rest : BlockWithin arithmetic module unit env (otherwise ++ following) bound) :
    BlockWithin arithmetic module unit env (.rangeStepLoop name next stop stride body otherwise :: following) (bound+1) := by
  obtain ⟨cost, value, bounded, run⟩ := rest
  refine ⟨rangeWork arithmetic next stop stride+cost, value, ?_, fun stack => ?_⟩
  · simp only [Nat.mul_add, Nat.mul_one]; omega
  · exact .next (by simp [step, inactive]) rfl (run stack)

theorem break_loop (positive : 1 ≤ unit) (target : loopTarget body = some (next, following))
    (rest : BlockWithin arithmetic module unit env following bound) :
    BlockWithin arithmetic module unit env (.breakLoop :: body) (bound+1) := by
  obtain ⟨cost, value, bounded, run⟩ := rest
  refine ⟨1+cost, value, ?_, fun stack => .next (by simp [step, target]) rfl (run stack)⟩
  simp only [Nat.mul_add, Nat.mul_one]; omega

theorem resume (positive : 1 ≤ unit)
    (rest : BlockWithin arithmetic module unit env (next :: following) bound) :
    BlockWithin arithmetic module unit env (.loopResume next :: following) (bound+1) := by
  obtain ⟨cost, value, bounded, run⟩ := rest
  refine ⟨1+cost, value, ?_, fun stack => .next rfl rfl (run stack)⟩
  simp only [Nat.mul_add, Nat.mul_one]; omega

end BlockWithin

namespace EvaluatesIn

inductive Arguments (arithmetic : PrimitiveWork.Arithmetic) (module : Module) (unit : Nat) (env : ScalarEnv) :
    List Expr → Nat → List Constant → Prop where
  | nil : Arguments arithmetic module unit env [] 0 []
  | cons : EvaluatesIn arithmetic module unit env expression cost value →
      Arguments arithmetic module unit env expressions tailCost values →
      Arguments arithmetic module unit env (expression :: expressions) (cost+tailCost+1) (value :: values)

theorem builtin_single (_positive : 1 ≤ unit)
    (argument : EvaluatesIn arithmetic module unit env a ca av)
    (result : Primitive.apply (.builtin builtin) [av] = some (.ok value))
    (priced : ∃ work, primitive arithmetic (.builtin builtin) [av] = some work ∧ work+1 ≤ unit) :
    EvaluatesIn arithmetic module unit env (.builtinCall builtin [a]) (ca+3) value := by
  obtain ⟨cost, bound, evaluated⟩ := argument
  obtain ⟨work, measured, workBound⟩ := priced
  refine ⟨cost+work+3, ?_, fun stack => ?_⟩
  · simp only [Nat.mul_add]; omega
  · have terminal : RuntimeCost.Reaches (step module) (charge arithmetic module)
        ⟨.primitive (.builtin builtin) [av], stack⟩ (work+1) ⟨.value value, stack⟩ := by
      apply RuntimeCost.Reaches.next (cost := 0) (following := ⟨.value value, stack⟩)
      · simp [step, outcome, result]
      · simp [charge, measured]
      · exact .refl
    have trace := RuntimeCost.Reaches.next (step := step module) (charge := charge arithmetic module)
      (state := ⟨.expr (.builtinCall builtin [a]) env, stack⟩) rfl rfl
      ((evaluated _).trans (.next rfl rfl terminal))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using trace

theorem unary (positive : 1 ≤ unit)
    (evaluated : EvaluatesIn arithmetic module unit env expression budget value)
    (result : scalarExpr (fun _ => none) (.unaryOp op (.constant value)) = some (.ok answer))
    (measured : ∀ stack, charge arithmetic module ⟨.value value, .unary op :: stack⟩ = some work)
    (priced : work ≤ unit) :
    EvaluatesIn arithmetic module unit env (.unaryOp op expression) (budget+2) answer := by
  obtain ⟨cost, bound, run⟩ := evaluated
  refine ⟨1+cost+work, ?_, fun stack => ?_⟩
  · simp only [Nat.mul_add]; omega
  · have trace := RuntimeCost.Reaches.next (step := step module) (charge := charge arithmetic module)
      (state := ⟨.expr (.unaryOp op expression) env, stack⟩) rfl rfl
      ((run _).trans (.next (following := ⟨.value answer, stack⟩)
        (by simp [step, outcome, result]) (measured stack) .refl))
    simpa only [Nat.add_zero, Nat.add_assoc] using trace

theorem conditional (positive : 1 ≤ unit)
    (condition : EvaluatesIn arithmetic module unit env test ct (.bool flag))
    (branch : EvaluatesIn arithmetic module unit env (if flag then yes else no) cb answer) :
    EvaluatesIn arithmetic module unit env (.ifExp test yes no) (ct+cb+2) answer := by
  obtain ⟨testCost, testBound, tested⟩ := condition
  obtain ⟨branchCost, branchBound, selected⟩ := branch
  refine ⟨testCost+branchCost+2, ?_, fun stack => ?_⟩
  · simp only [Nat.mul_add]; omega
  · have trace := RuntimeCost.Reaches.next (step := step module) (charge := charge arithmetic module)
      (state := ⟨.expr (.ifExp test yes no) env, stack⟩) rfl rfl
      ((tested _).trans (.next rfl rfl (selected stack)))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using trace

end EvaluatesIn

private def rangeState (name : String) (env : ScalarEnv) (done : List Constant)
    (expressions : List Expr) (body otherwise following : List Stmt) (stack : List Frame) : State :=
  match expressions with
  | [] => ⟨.startRange name done body otherwise following env, stack⟩
  | first :: rest => ⟨.expr first env, .rangeArguments name done rest body otherwise following env :: stack⟩

private theorem range_reach (h : EvaluatesIn.Arguments arithmetic module unit env expressions budget values)
    (done : List Constant) (small : done.length+expressions.length ≤ unit) :
    ∃ cost, cost ≤ unit*budget ∧ ∀ stack,
      RuntimeCost.Reaches (step module) (charge arithmetic module)
        (rangeState name env done expressions body otherwise following stack) cost
        ⟨.startRange name (done ++ values) body otherwise following env, stack⟩ := by
  induction h generalizing done with
  | nil => exact ⟨0, by simp, fun _ => by simp [rangeState]; exact .refl⟩
  | @cons expression budget value expressions tailBudget values head tail ih =>
      obtain ⟨headCost, headBound, evaluated⟩ := head
      obtain ⟨tailCost, tailBound, run⟩ := ih (done ++ [value]) (by simp only [List.length_append, List.length_cons, List.length_nil] at *; omega)
      refine ⟨headCost+(done.length+1)+tailCost, ?_, fun stack => ?_⟩
      · have frameBound : done.length+1 ≤ unit := by simp only [List.length_cons] at small; omega
        simp only [Nat.mul_add, Nat.mul_one]; omega
      · have trace := (evaluated (.rangeArguments name done expressions body otherwise following env :: stack)).trans
          (RuntimeCost.Reaches.next rfl rfl (run stack))
        simpa [rangeState, List.append_assoc, Nat.add_assoc] using trace

theorem BlockWithin.for_range (positive : 1 ≤ unit)
    (arguments : EvaluatesIn.Arguments arithmetic module unit env expressions budget values)
    (small : expressions.length ≤ unit) (priced : argumentWork arithmetic values ≤ unit)
    (bounds : rangeBounds values = .ok (start, stop, stride))
    (rest : BlockWithin arithmetic module unit env (.rangeStepLoop name start stop stride body otherwise :: following) bound) :
    BlockWithin arithmetic module unit env (.forIn (.name name) (.call (.name "range") expressions) body otherwise :: following)
      (budget+2+bound) := by
  obtain ⟨headCost, headBound, head⟩ := range_reach arguments [] (by simpa using small)
  obtain ⟨tailCost, answer, tailBound, tail⟩ := rest
  refine ⟨1+headCost+argumentWork arithmetic values+tailCost, answer, ?_, fun stack => ?_⟩
  · simp only [Nat.mul_add]; omega
  · have trace := RuntimeCost.Reaches.next (step := step module) (charge := charge arithmetic module)
      (state := ⟨.block (.forIn (.name name) (.call (.name "range") expressions) body otherwise :: following) env, stack⟩)
      rfl rfl ((head stack).trans (.next (by simp [step, bounds]) rfl (tail stack)))
    simpa [rangeState, Nat.add_assoc] using trace

end FormalSW.PyAst.Calls.Runtime.Scaled
