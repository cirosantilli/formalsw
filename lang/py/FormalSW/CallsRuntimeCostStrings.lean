import lang.py.FormalSW.CallsRuntimeCostBlocks
import lang.py.FormalSW.DecimalWorkBounds

namespace FormalSW.PyAst.Calls.Runtime

/-- The Python expression `name[::-1]`, including evaluation of its slice bounds. -/
def reverseString (name : String) : Expr :=
  .subscript (.name name) (.slice none none (some (.unaryOp .uSub (.constant (.int 1)))))

theorem EvaluatesIn.reverse_string (found : env name = some (.string text)) :
    EvaluatesIn .word module env (reverseString name) (text.length+27)
      (.string (String.ofList text.toList.reverse)) := by
  intro stack
  let frame := Frame.primitiveArguments .slice []
    [.constant .none, .constant .none, .unaryOp .uSub (.constant (.int 1))] env
  have start : RuntimeCost.Reaches (step module) (charge .word module)
      ⟨.expr (reverseString name) env, stack⟩ 1 ⟨.expr (.name name) env, frame :: stack⟩ := by
    runtime_step
    exact .refl
  have rest : RuntimeCost.Reaches (step module) (charge .word module)
      ⟨.value (.string text), frame :: stack⟩ 16
      ⟨.primitive .slice [.string text, .none, .none, .int (-1)], stack⟩ := by
    repeat first | exact RuntimeCost.Reaches.refl | runtime_step
  have tail : RuntimeCost.Reaches (step module) (charge .word module)
      ⟨.primitive .slice [.string text, .none, .none, .int (-1)], stack⟩ (text.length+9)
      ⟨.value (.string (String.ofList text.toList.reverse)), stack⟩ := by
    apply RuntimeCost.Reaches.next (cost := 0) (following := ⟨.value (.string (String.ofList text.toList.reverse)), stack⟩)
    · simp [step, outcome, Primitive.apply, Strings.slice_reverse]
    · simp only [charge, primitive, argumentWork, PrimitiveWork.scalarSize, PrimitiveWork.integer,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Option.map_some]
      congr 1 <;> omega
    · exact .refl
  have trace := ((start.trans (EvaluatesIn.lookup found _)).trans rest).trans tail
  simpa only [show 1+1+16+(text.length+9) = text.length+27 by omega] using trace

end FormalSW.PyAst.Calls.Runtime
