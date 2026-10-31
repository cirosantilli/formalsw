import lang.py.FormalSW.HeapCalls

/-! Truth-valued reasoning for heap-preserving expressions whose Python results need not be booleans. -/
namespace FormalSW.PyAst.HeapCalls

/-- The expression returns a value with the specified truth value, preserving the heap. -/
def EvaluatesTruth (module : Module) (env : Env) (expression : Expr)
    (heap : Heap) (flag : Bool) (globals : Mutable.Globals := []) : Prop :=
  ∃ value, Evaluates module env expression heap value heap globals ∧
    Mutable.truth value heap = some (.ok flag, heap)

namespace EvaluatesTruth
variable {module : Module} {env : Env} {heap : Heap} {globals : Mutable.Globals}
    {left right : Expr} {a b : Bool}

/-- Python `and` returns an operand; this rule tracks its truth without changing that result. -/
theorem and (first : EvaluatesTruth module env left heap a globals)
    (second : EvaluatesTruth module env right heap b globals) :
    EvaluatesTruth module env (.boolOp .and [left, right]) heap (a && b) globals := by
  obtain ⟨av, evaluatedA, truthA⟩ := first
  cases a with
  | false => exact ⟨av, Evaluates.boolean_stop evaluatedA truthA rfl, truthA⟩
  | true =>
      obtain ⟨bv, evaluatedB, truthB⟩ := second
      exact ⟨bv, Evaluates.boolean_next evaluatedA truthA rfl
        (Evaluates.boolean_last evaluatedB truthB), truthB⟩

/-- Python `or` only reaches the second operand when the first is false. -/
theorem or (first : EvaluatesTruth module env left heap a globals)
    (second : EvaluatesTruth module env right heap b globals) :
    EvaluatesTruth module env (.boolOp .or [left, right]) heap (a || b) globals := by
  obtain ⟨av, evaluatedA, truthA⟩ := first
  cases a with
  | true => exact ⟨av, Evaluates.boolean_stop evaluatedA truthA rfl, truthA⟩
  | false =>
      obtain ⟨bv, evaluatedB, truthB⟩ := second
      exact ⟨bv, Evaluates.boolean_next evaluatedA truthA rfl
        (Evaluates.boolean_last evaluatedB truthB), truthB⟩

/-- Unlike `and` and `or`, `not` always returns a boolean. -/
theorem not (evaluated : EvaluatesTruth module env left heap a globals) :
    Evaluates module env (.unaryOp .not left) heap (.scalar (.bool (!a))) heap globals := by
  obtain ⟨value, result, truth⟩ := evaluated
  apply Evaluates.unary result
  simp [HeapCalls.unary, truth]

end EvaluatesTruth
end FormalSW.PyAst.HeapCalls
