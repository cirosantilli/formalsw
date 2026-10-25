import lang.py.FormalSW.Calls

/-! Reuse a fully supplied scalar-call proof when trailing Python defaults are omitted. -/
namespace FormalSW.PyAst.Calls

/-- Omitted arguments enter the same proved body with the completed argument vector. -/
theorem ReturnsValue.with_defaults
    (found : findFunctionIn module.body name = some (args, body))
    (omitted : args.length ≠ supplied.length)
    (filled : completeArguments args supplied = some values)
    (complete : args.length = values.length)
    (executed : ReturnsValue module name values value) :
    ReturnsValue module name supplied value := by
  intro stack
  cases executed stack with
  | next transition rest =>
      simp only [step, found, complete, if_true, protectGenerator_next,
        Step.next.injEq] at transition
      subst transition
      exact .next (by simp [step, found, omitted, filled, protectGenerator_next]) rest

end FormalSW.PyAst.Calls
