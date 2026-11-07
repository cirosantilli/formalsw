import lang.py.FormalSW.HeapRuntimeCostReverseLoops

namespace ReverseLoopsRuntimeRegression
open FormalSW.PyAst HeapCalls HeapCalls.Runtime PrimitiveWork
private def program : Module := { body := [] }

/-- The complete iterator visits a list backwards without allocating a copy. -/
theorem iterate (items : List Mutable.Value) (count : Nat) (bound : count ≤ items.length)
    (env : Mutable.Env) :
    ∃ finalEnv, BlockContinuesIn .word program env
      [.reverseSequenceStepLoop "v" (.ref 0) ((count : Int) - 1) [] []]
      [.list items] (5 * count + 2) finalEnv [.list items] := by
  induction count generalizing env with
  | zero => exact ⟨env, BlockContinuesIn.reverse_done (by decide) BlockContinuesIn.nil⟩
  | succ count ih =>
      have inside : count < items.length := by omega
      obtain ⟨finalEnv, rest⟩ := ih (by omega) (setLocal env "v" items[count])
      refine ⟨finalEnv, ?_⟩
      have run := BlockContinuesIn.reverse_list_step (globals := []) (arithmetic := .word)
        (module := program) (env := env) (name := "v") (body := []) (otherwise := [])
        (position := (count : Int)) (by omega) (address := 0) (items := items)
        (show [Mutable.Object.list items][0]? = some (.list items) from rfl)
        (value := items[count]) (List.getElem?_eq_getElem inside) rest
      simpa [Calls.loopContinuation, Nat.mul_add, Nat.add_assoc] using run

example (items : List Mutable.Value) :
    ∃ finalEnv, BlockContinuesIn .word program (fun _ => some (.ref 0))
      [.forReversed "v" (.name "items") [] []]
      [.list items] (5 * items.length + 7) finalEnv [.list items] := by
  obtain ⟨finalEnv, rest⟩ := iterate items items.length (by omega) (fun _ => some (.ref 0))
  refine ⟨finalEnv, ?_⟩
  exact (BlockContinuesIn.for_reversed_list (EvaluatesIn.lookup rfl) rfl rest).mono (by
    simp only [integer]; omega)

/-- Cursor arithmetic is bit-sensitive even though reading one reference is fixed. -/
example : charge .bits program
    ⟨.block [.reverseSequenceStepLoop "v" (.ref 0) (2^100) [] []] (fun _ => none), [], [.list []]⟩ =
      some 205 := by decide
example : charge .word program
    ⟨.block [.reverseSequenceStepLoop "v" (.ref 0) (2^100) [] []] (fun _ => none), [], [.list []]⟩ =
      some 5 := by decide

/-- An exhausted iterator stops before accessing a stale receiver. -/
example : RuntimeCost.Finishes (HeapCalls.step program 0) (charge .word program)
    ⟨.block [.reverseSequenceStepLoop "v" (.ref 999) (-1) [] []] (fun _ => none), [], []⟩ 4
    (.ok ⟨.ok (.scalar .none), [], [], 0⟩) := by
  refine RuntimeCost.Finishes.next (amount := 2) (cost := 2)
    (following := ⟨.block [] (fun _ => none), [], []⟩) ?_ ?_ ?_
  · rfl
  · rfl
  · refine RuntimeCost.Finishes.next (amount := 1) (cost := 1)
      (following := ⟨.value (.scalar .none), [], []⟩) ?_ ?_ ?_
    · rfl
    · rfl
    · exact .done rfl rfl


/-- Unsupported reversible protocols stay unpriced. -/
example : charge .word program
    ⟨.value (.ref 0), [.reverseSequence "v" [] [] [] (fun _ => none)], [.dict []]⟩ = none := rfl

#print axioms iterate
#print axioms BlockContinuesIn.for_reversed_list
#print axioms BlockContinuesIn.reverse_list_step
#print axioms BlockContinuesIn.reverse_done
end ReverseLoopsRuntimeRegression
