import lang.py.FormalSW.HeapCalls

/-! Parsing-oriented string methods preserve receiver and argument effects. -/
namespace FormalSW.PyAst.HeapCalls.Evaluates
variable {globals : Mutable.Globals}

theorem split_lines (receiver : Evaluates (globals := globals) module env base heap (.scalar (.string text)) middle)
    (localName : ∀ name, base = .name name → (env name).isSome = true) :
    Evaluates (globals := globals) module env (.call (.attribute base "splitlines") []) heap (.ref middle.length)
      (middle ++ [.list ((Strings.splitLines text).map fun line => .scalar (.string line))]) := by
  intro anchors stack
  apply Reaches.next (following := ⟨.expr base env, .methodReceiver "splitlines" [] env :: stack, heap⟩)
    (by cases base <;> simp_all [step])
  apply (receiver anchors _).trans
  apply Reaches.next (following := argumentsState (.splitLines text) env [] [] stack middle)
    (by simp [step, run, bindMethod])
  exact .next (by simp [argumentsState, step, result, run, primitive, Mutable.allocate, Except.map]) .refl

theorem starts_with (receiver : Evaluates (globals := globals) module env base heap (.scalar (.string text)) middle)
    (argument : Evaluates (globals := globals) module env expression middle (.scalar (.string expected)) afterArgument)
    (localName : ∀ name, base = .name name → (env name).isSome = true) :
    Evaluates (globals := globals) module env (.call (.attribute base "startswith") [expression]) heap
      (.scalar (.bool (Strings.startsWith text expected))) afterArgument := by
  intro anchors stack
  apply Reaches.next (following := ⟨.expr base env, .methodReceiver "startswith" [expression] env :: stack, heap⟩)
    (by cases base <;> simp_all [step])
  apply (receiver anchors _).trans
  apply Reaches.next (following := argumentsState (.startsWith text) env [] [expression] stack middle)
    (by simp [step, run, bindMethod])
  apply (arguments_reach (.cons argument .nil) (.startsWith text) [] anchors stack).trans
  exact .next (by simp [step, result, run, primitive]) .refl

end FormalSW.PyAst.HeapCalls.Evaluates
