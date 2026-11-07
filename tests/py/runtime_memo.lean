import lang.py.FormalSW.MemoRuntimeCostFunctions

namespace MemoRuntimeRegression
open FormalSW.PyAst MemoCalls MemoCalls.Runtime

private def program : Module := { body := [
  .functionDef "score" [⟨"n", none, none⟩] none
    [.return (.binOp (.name "n") .add (.constant (.int 1)))],
  .functionDef "solve" [] none
    [.return (.binOp (.call (.name "score") [.constant (.int 3)]) .add
      (.call (.name "score") [.constant (.int 3)]))]] }
private def key : Key := ⟨"score", [3], none⟩

/-- The first call misses and writes; the second call hits the same actual cache. -/
theorem repeated_call : RuntimeCost.Finishes (Runtime.step program ["score"])
    (charge .word program ["score"]) (Runtime.function program ["score"] "solve" []).initial
    44 (.ok (.int 8)) := by
  have run : RuntimeCost.Reaches (Runtime.step program ["score"]) (charge .word program ["score"])
      (Runtime.function program ["score"] "solve" []).initial 43
      ⟨⟨⟨.value (.int 8), []⟩, [], Cache.empty.insert key (.int 4)⟩, [key]⟩ := by
    repeat first | exact RuntimeCost.Reaches.refl | runtime_step
  exact run.finishes (.done rfl rfl)

example : TimeBound .word program ["score"] "solve" [] 44 :=
  ⟨44, .ok (.int 8), repeated_call, Nat.le_refl _⟩

/-- Replacing an existing entry does not increase the table-size metadata. -/
example : nextKeys ⟨⟨⟨.value (.int 5), []⟩, [⟨key, []⟩],
    Cache.empty.insert key (.int 4)⟩, [key]⟩ = [key] := by decide

example : Represents [key] (Cache.empty.insert key (.int 4)) := by
  simpa [recordKey] using represents_empty.insert key (.int 4)

/-- Key widths and occupied slots both affect lookup, even in the word model. -/
example : lookupWork .word [] key = some 3 := rfl
example : lookupWork .word [key] key = some 10 := rfl
example : lookupWork .bits [] (⟨"score", [2^100], none⟩ : Key) = some 103 := by decide
example : lookupWork .word [] (⟨"score", [], some []⟩ : Key) = none := rfl

#print axioms represents_next
#print axioms represents_reaches
#print axioms function_equiv
#print axioms RunsIn.raw
#print axioms RunsIn.trans
#print axioms BlockReturnsIn.memoized_function
#print axioms ReturnsIn.timeBound
#print axioms repeated_call

end MemoRuntimeRegression
