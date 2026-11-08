import lang.py.FormalSW.CallsRuntimeCostControl

/-! Compose runtime bounds using a common upper bound per source-machine step.
Every arithmetic operation still requires its actual tariff and an operand-size
bound. Missing tariffs cannot be replaced by the scaling factor. -/
namespace FormalSW.PyAst.Calls.Runtime.Scaled

def Reaches (arithmetic : PrimitiveWork.Arithmetic) (module : Module) (unit : Nat)
    (initial : State) (budget : Nat) (final : State) : Prop :=
  ∃ cost, cost ≤ unit * budget ∧
    RuntimeCost.Reaches (step module) (charge arithmetic module) initial cost final

namespace Reaches

theorem refl : Reaches arithmetic module unit state 0 state := ⟨0, by simp, .refl⟩

theorem next (transition : step module state = .next following)
    (priced : ∃ amount, charge arithmetic module state = some amount ∧ amount ≤ unit)
    (rest : Reaches arithmetic module unit following budget final) :
    Reaches arithmetic module unit state (1 + budget) final := by
  obtain ⟨amount, measured, small⟩ := priced
  obtain ⟨cost, bound, run⟩ := rest
  exact ⟨amount + cost, by simpa [Nat.mul_add] using Nat.add_le_add small bound,
    .next transition measured run⟩

theorem trans (first : Reaches arithmetic module unit a ca b)
    (second : Reaches arithmetic module unit b cb c) :
    Reaches arithmetic module unit a (ca + cb) c := by
  obtain ⟨costA, boundA, runA⟩ := first
  obtain ⟨costB, boundB, runB⟩ := second
  exact ⟨costA + costB, by simpa [Nat.mul_add] using Nat.add_le_add boundA boundB,
    runA.trans runB⟩

theorem mono (run : Reaches arithmetic module unit a small b) (bound : small ≤ large) :
    Reaches arithmetic module unit a large b := by
  obtain ⟨cost, upper, run⟩ := run
  exact ⟨cost, Nat.le_trans upper (Nat.mul_le_mul_left unit bound), run⟩

end Reaches

def EvaluatesIn (arithmetic : PrimitiveWork.Arithmetic) (module : Module) (unit : Nat)
    (env : ScalarEnv) (expression : Expr) (budget : Nat) (value : Constant) : Prop :=
  ∃ cost, cost ≤ unit * budget ∧ Runtime.EvaluatesIn arithmetic module env expression cost value

namespace EvaluatesIn

theorem reaches (evaluated : EvaluatesIn arithmetic module unit env expression budget value)
    (stack : List Frame) :
    Reaches arithmetic module unit ⟨.expr expression env, stack⟩ budget ⟨.value value, stack⟩ := by
  obtain ⟨cost, bound, run⟩ := evaluated
  exact ⟨cost, bound, run stack⟩

theorem constant (positive : 1 ≤ unit) :
    EvaluatesIn arithmetic module unit env (.constant value) 1 value :=
  ⟨1, by simpa using positive, Runtime.EvaluatesIn.constant⟩

theorem lookup (positive : 1 ≤ unit) (found : env name = some value) :
    EvaluatesIn arithmetic module unit env (.name name) 1 value :=
  ⟨1, by simpa using positive, Runtime.EvaluatesIn.lookup found⟩

theorem binary (_positive : 1 ≤ unit)
    (left : EvaluatesIn arithmetic module unit env a ca av)
    (right : EvaluatesIn arithmetic module unit env b cb bv)
    (result : scalarBinary op av bv = some (.ok value))
    (priced : ∃ work, PrimitiveWork.binary arithmetic op av bv = some work ∧ work + 1 ≤ unit) :
    EvaluatesIn arithmetic module unit env (.binOp a op b) (ca + cb + 3) value := by
  obtain ⟨costA, boundA, runA⟩ := left
  obtain ⟨costB, boundB, runB⟩ := right
  obtain ⟨work, measured, boundWork⟩ := priced
  refine ⟨costA + costB + work + 3, ?_, Runtime.EvaluatesIn.binary runA runB result measured⟩
  simp only [Nat.mul_add]
  omega

/-- Library work may consume several units of the common operation budget. -/
theorem library_single (positive : 1 ≤ unit)
    (argument : EvaluatesIn arithmetic module unit env a ca av)
    (absent : findFunctionIn module.body name = none)
    (result : libraryCall module name [av] = some (.ok value))
    (priced : ∃ work, library arithmetic module name [av] = some work ∧ work+1 ≤ unit*invokeBudget) :
    EvaluatesIn arithmetic module unit env (.call (.name name) [a]) (ca+2+invokeBudget) value := by
  obtain ⟨cost, bound, evaluated⟩ := argument
  obtain ⟨work, measured, workBound⟩ := priced
  refine ⟨cost+work+3, ?_, ?_⟩
  · simp only [Nat.mul_add]
    omega
  · intro stack
    have run := RuntimeCost.Reaches.next (charge := charge arithmetic module) (step := step module)
      (state := ⟨.expr (.call (.name name) [a]) env, stack⟩) rfl rfl
      ((evaluated _).trans (.next rfl rfl
        (.next (amount := work+1) (following := ⟨.value value, stack⟩)
          (by simp [step, absent, outcome, result]) (by simp [charge, absent, measured]) .refl)))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

theorem compare (_positive : 1 ≤ unit)
    (left : EvaluatesIn arithmetic module unit env a ca av)
    (right : EvaluatesIn arithmetic module unit env b cb bv)
    (result : scalarCompare op av bv = some value)
    (priced : PrimitiveWork.comparison arithmetic av bv + 1 ≤ unit) :
    EvaluatesIn arithmetic module unit env (.compare a [(op, b)]) (ca + cb + 3) (.bool value) := by
  obtain ⟨costA, boundA, runA⟩ := left
  obtain ⟨costB, boundB, runB⟩ := right
  refine ⟨costA + costB + PrimitiveWork.comparison arithmetic av bv + 3, ?_,
    Runtime.EvaluatesIn.compare runA runB result⟩
  simp only [Nat.mul_add]
  omega

end EvaluatesIn

theorem assign (positive : 1 ≤ unit)
    (evaluated : EvaluatesIn arithmetic module unit env expression budget value)
    (name : String) (following : List Stmt) (stack : List Frame) :
    Reaches arithmetic module unit ⟨.block (.assign [.name name] expression :: following) env, stack⟩
      (budget + 2) ⟨.block following (env.set name value), stack⟩ := by
  obtain ⟨cost, bound, run⟩ := evaluated
  exact ⟨cost + 2, by simp only [Nat.mul_add]; omega, Runtime.assign run name following stack⟩

theorem augAssign (positive : 1 ≤ unit)
    (evaluated : EvaluatesIn arithmetic module unit env (.binOp (.name name) op expression) budget value)
    (following : List Stmt) (stack : List Frame) :
    Reaches arithmetic module unit ⟨.block (.augAssign (.name name) op expression :: following) env, stack⟩
      (budget + 2) ⟨.block following (env.set name value), stack⟩ := by
  obtain ⟨cost, bound, run⟩ := evaluated
  exact ⟨cost + 2, by simp only [Nat.mul_add]; omega, Runtime.augAssign run following stack⟩

theorem branch (positive : 1 ≤ unit)
    (evaluated : EvaluatesIn arithmetic module unit env condition budget (.bool test))
    (yes no following : List Stmt) (stack : List Frame) :
    Reaches arithmetic module unit ⟨.block (.ifThen condition yes no :: following) env, stack⟩
      (budget + 2) ⟨.block ((if test then yes else no) ++ following) env, stack⟩ := by
  obtain ⟨cost, bound, run⟩ := evaluated
  exact ⟨cost + 2, by simp only [Nat.mul_add]; omega, Runtime.branch run yes no following stack⟩

theorem whileTest (positive : 1 ≤ unit)
    (evaluated : EvaluatesIn arithmetic module unit env condition budget (.bool test))
    (body otherwise following : List Stmt) (stack : List Frame) :
    Reaches arithmetic module unit ⟨.block (.whileDo condition body otherwise :: following) env, stack⟩
      (budget + 2)
      ⟨.block ((if test then body ++ [loopContinuation body (.whileDo condition body otherwise)]
        else otherwise) ++ following) env, stack⟩ := by
  obtain ⟨cost, bound, run⟩ := evaluated
  exact ⟨cost + 2, by simp only [Nat.mul_add]; omega, Runtime.whileTest run body otherwise following stack⟩

end FormalSW.PyAst.Calls.Runtime.Scaled
