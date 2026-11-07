import lang.py.FormalSW.MemoRuntimeCostFunctions

/-! Compositional expression and block budgets for the memoized interpreter.
Primitive work is measured under the selected arithmetic policy; `RunsIn`
accounts for cache growth and collision-chain lookup in its runtime envelope. -/
namespace FormalSW.PyAst.MemoCalls.Runtime

namespace EvaluatesIn

theorem mono (run : EvaluatesIn arithmetic module memoized spec width env expression a value)
    (larger : a ≤ b) : EvaluatesIn arithmetic module memoized spec width env expression b value :=
  fun stack => (run stack).mono larger

theorem constant :
    EvaluatesIn arithmetic module memoized spec width env (.constant value) 1 value := by
  intro stack
  exact RunsIn.raw
    (initial := ⟨.expr (.constant value) env, stack⟩)
    (following := ⟨.value value, stack⟩) (by trivial) rfl rfl

theorem lookup (found : env name = some value) :
    EvaluatesIn arithmetic module memoized spec width env (.name name) 1 value := by
  intro stack
  exact RunsIn.raw
    (initial := ⟨.expr (.name name) env, stack⟩)
    (following := ⟨.value value, stack⟩) (by trivial)
    (by simp [Calls.step, Calls.outcome, found]) rfl

theorem binary (left : EvaluatesIn arithmetic module memoized spec width env a ca av)
    (right : EvaluatesIn arithmetic module memoized spec width env b cb bv)
    (result : scalarBinary op av bv = some (.ok value))
    (measured : PrimitiveWork.binary arithmetic op av bv = some work) :
    EvaluatesIn arithmetic module memoized spec width env (.binOp a op b)
      (ca + cb + work + 3) value := by
  intro stack
  have enter : RunsIn arithmetic module memoized spec width
      ⟨.expr (.binOp a op b) env, stack⟩ 1
      ⟨.expr a env, .binaryLeft op b env :: stack⟩ :=
    RunsIn.raw (initial := ⟨.expr (.binOp a op b) env, stack⟩)
      (following := ⟨.expr a env, .binaryLeft op b env :: stack⟩)
      (by trivial) rfl rfl
  have finish : RunsIn arithmetic module memoized spec width
      ⟨.value bv, .binaryRight op av :: stack⟩ (work + 1) ⟨.value value, stack⟩ :=
    RunsIn.raw (initial := ⟨.value bv, .binaryRight op av :: stack⟩)
      (following := ⟨.value value, stack⟩) (by trivial)
      (by simp [Calls.step, Calls.outcome, result])
      (by simp [Calls.Runtime.charge, measured])
  have run := enter.trans ((left _).trans
    ((RunsIn.raw (initial := ⟨.value av, .binaryLeft op b env :: stack⟩)
      (following := ⟨.expr b env, .binaryRight op av :: stack⟩)
      (amount := 1) (by trivial) rfl rfl).trans ((right _).trans finish)))
  exact run.mono (by omega)

theorem compare (left : EvaluatesIn arithmetic module memoized spec width env a ca av)
    (right : EvaluatesIn arithmetic module memoized spec width env b cb bv)
    (result : scalarCompare op av bv = some answer) :
    EvaluatesIn arithmetic module memoized spec width env (.compare a [(op, b)])
      (ca + cb + PrimitiveWork.comparison arithmetic av bv + 3) (.bool answer) := by
  intro stack
  have enter : RunsIn arithmetic module memoized spec width
      ⟨.expr (.compare a [(op, b)]) env, stack⟩ 1
      ⟨.expr a env, .compareLeft op b env :: stack⟩ :=
    RunsIn.raw (initial := ⟨.expr (.compare a [(op, b)]) env, stack⟩)
      (following := ⟨.expr a env, .compareLeft op b env :: stack⟩)
      (by trivial) rfl rfl
  have finish : RunsIn arithmetic module memoized spec width
      ⟨.value bv, .compareRight op av :: stack⟩
      (PrimitiveWork.comparison arithmetic av bv + 1) ⟨.value (.bool answer), stack⟩ :=
    RunsIn.raw (initial := ⟨.value bv, .compareRight op av :: stack⟩)
      (following := ⟨.value (.bool answer), stack⟩) (by trivial)
      (by simp [Calls.step, Calls.outcome, result]) rfl
  have run := enter.trans ((left _).trans
    ((RunsIn.raw (initial := ⟨.value av, .compareLeft op b env :: stack⟩)
      (following := ⟨.expr b env, .compareRight op av :: stack⟩)
      (amount := 1) (by trivial) rfl rfl).trans ((right _).trans finish)))
  exact run.mono (by omega)

theorem conditional
    (condition : EvaluatesIn arithmetic module memoized spec width env test ct c)
    (branch : EvaluatesIn arithmetic module memoized spec width env
      (if scalarTruth c then yes else no) cb value) :
    EvaluatesIn arithmetic module memoized spec width env (.ifExp test yes no)
      (ct + cb + 2) value := by
  intro stack
  have enter : RunsIn arithmetic module memoized spec width
      ⟨.expr (.ifExp test yes no) env, stack⟩ 1
      ⟨.expr test env, .conditional yes no env :: stack⟩ :=
    RunsIn.raw (initial := ⟨.expr (.ifExp test yes no) env, stack⟩)
      (following := ⟨.expr test env, .conditional yes no env :: stack⟩)
      (by trivial) rfl rfl
  have run := enter.trans ((condition _).trans
    ((RunsIn.raw (initial := ⟨.value c, .conditional yes no env :: stack⟩)
      (following := ⟨.expr (if scalarTruth c then yes else no) env, stack⟩)
      (amount := 1) (by trivial) rfl rfl).trans (branch stack)))
  exact run.mono (by omega)

theorem call_single (argument : EvaluatesIn arithmetic module memoized spec width env a ca av)
    (result : ReturnsIn arithmetic module memoized spec width name [av] cc value) :
    EvaluatesIn arithmetic module memoized spec width env (.call (.name name) [a])
      (ca + cc + 2) value := by
  intro stack
  have enter : RunsIn arithmetic module memoized spec width
      ⟨.expr (.call (.name name) [a]) env, stack⟩ 1
      ⟨.expr a env, .arguments name [] [] env :: stack⟩ :=
    RunsIn.raw (initial := ⟨.expr (.call (.name name) [a]) env, stack⟩)
      (following := ⟨.expr a env, .arguments name [] [] env :: stack⟩)
      (by trivial) rfl rfl
  have run := enter.trans ((argument _).trans
    ((RunsIn.raw (initial := ⟨.value av, .arguments name [] [] env :: stack⟩)
      (following := ⟨.invoke name [av], stack⟩)
      (amount := 1) (by trivial) rfl rfl).trans (result stack)))
  exact run.mono (by omega)

end EvaluatesIn

namespace BlockReturnsIn

theorem mono (run : BlockReturnsIn arithmetic module memoized spec width env body a value)
    (larger : a ≤ b) : BlockReturnsIn arithmetic module memoized spec width env body b value :=
  fun stack => (run stack).mono larger

theorem return_value
    (run : EvaluatesIn arithmetic module memoized spec width env expression ce value) :
    BlockReturnsIn arithmetic module memoized spec width env (.return expression :: rest)
      (ce + 1) value := by
  intro stack
  have enter : RunsIn arithmetic module memoized spec width
      ⟨.block (.return expression :: rest) env, stack⟩ 1 ⟨.expr expression env, stack⟩ :=
    RunsIn.raw (initial := ⟨.block (.return expression :: rest) env, stack⟩)
      (following := ⟨.expr expression env, stack⟩) (by trivial) rfl rfl
  exact (enter.trans (run stack)).mono (by omega)

theorem branch
    (test : EvaluatesIn arithmetic module memoized spec width env condition ct value)
    (rest : BlockReturnsIn arithmetic module memoized spec width env
      ((if scalarTruth value then yes else no) ++ body) cr result) :
    BlockReturnsIn arithmetic module memoized spec width env (.ifThen condition yes no :: body)
      (ct + cr + 2) result := by
  intro stack
  have enter : RunsIn arithmetic module memoized spec width
      ⟨.block (.ifThen condition yes no :: body) env, stack⟩ 1
      ⟨.expr condition env, .branch yes no body env :: stack⟩ :=
    RunsIn.raw (initial := ⟨.block (.ifThen condition yes no :: body) env, stack⟩)
      (following := ⟨.expr condition env, .branch yes no body env :: stack⟩)
      (by trivial) rfl rfl
  have run := enter.trans ((test _).trans
    ((RunsIn.raw (initial := ⟨.value value, .branch yes no body env :: stack⟩)
      (following := ⟨.block ((if scalarTruth value then yes else no) ++ body) env, stack⟩)
      (amount := 1) (by trivial) rfl rfl).trans (rest stack)))
  exact run.mono (by omega)

end BlockReturnsIn

end FormalSW.PyAst.MemoCalls.Runtime
