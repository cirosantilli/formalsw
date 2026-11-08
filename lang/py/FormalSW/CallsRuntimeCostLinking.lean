import lang.py.FormalSW.Linking
import lang.py.FormalSW.CallsRuntimeCostScaled

/-! Linking preserves both execution and its prices. Semantic extension alone
is insufficient for cost transfer: library bindings must keep their cost models. -/
namespace FormalSW.PyAst.Calls.Runtime

theorem charge_extend (extension : Extends target source)
    (imports : ∀ name, importedFunction target.body name = importedFunction source.body name)
    (state : State) (supported : step source state ≠ .unsupported) :
    charge arithmetic target state = charge arithmetic source state := by
  rcases state with ⟨work, stack⟩
  cases work with
  | invoke name values =>
      cases found : findFunctionIn source.body name with
      | some declaration =>
          rcases declaration with ⟨args, body⟩
          simp [charge, found, extension.functions name args body found]
      | none =>
          cases result : libraryCall source name values with
          | none => simp [step, found, result, outcome] at supported
          | some answer =>
              have preserved := extension.libraries name values answer found result
              simp [charge, found, preserved.1, library, imports name]
  | block body env =>
      cases body with
      | nil => rfl
      | cons statement rest => cases statement <;> rfl
  | _ => rfl

theorem reaches_extend (run : RuntimeCost.Reaches (step source) (charge arithmetic source) initial cost final)
    (extension : Extends target source)
    (imports : ∀ name, importedFunction target.body name = importedFunction source.body name) :
    RuntimeCost.Reaches (step target) (charge arithmetic target) initial cost final := by
  induction run with
  | refl => exact .refl
  | @next state following amount restCost final transition measured rest ih =>
      have supported : step source state ≠ .unsupported := by simp [transition]
      exact .next (by rw [extension.step_eq state supported]; exact transition)
        (by rw [charge_extend extension imports state supported]; exact measured) ih

theorem Scaled.Reaches.extend (run : Scaled.Reaches arithmetic source unit initial budget final)
    (extension : Extends target source)
    (imports : ∀ name, importedFunction target.body name = importedFunction source.body name) :
    Scaled.Reaches arithmetic target unit initial budget final := by
  obtain ⟨cost, bounded, trace⟩ := run
  exact ⟨cost, bounded, reaches_extend trace extension imports⟩

end FormalSW.PyAst.Calls.Runtime
