import lang.py.FormalSW.HeapRuntimeCostExtrema

open FormalSW.PyAst HeapCalls HeapCalls.Runtime
private def program : Module := { body := [] }

/-- Fixed arithmetic does not make a whole maximum scan constant time. -/
example : charge .word program
    ⟨.operation (.builtin .max) [.ref 0], [], [.list (List.replicate 10 (.scalar (.int (2^100))))]⟩ = some 34 := by decide
example : charge .bits program
    ⟨.operation (.builtin .max) [.ref 0], [], [.list (List.replicate 10 (.scalar (.int (2^100))))]⟩ = some 2234 := by decide
example : charge .word program
    ⟨.operation (.builtin .min) [.ref 0], [], [.tuple [.scalar (.int 7), .scalar (.int (-3))]]⟩ = some 10 := by decide
example : charge .word program
    ⟨.operation (.builtin .max) [.ref 0], [], [.list [.ref 0]]⟩ = none := rfl

example (first : Int) (rest : List Int) (heap : Heap) (address : Nat)
    (found : heap[address]? = some (.list ((first :: rest).map (fun value => .scalar (.int value))))) :
    EvaluatesIn .word program (fun _ => some (.ref address)) (.builtinCall .max [.name "xs"])
      heap (3*(rest.length+2)+4) (.scalar (.int (rest.foldl max first))) heap := by
  have run := EvaluatesIn.list_maximum (arithmetic := .word) (module := program)
    (env := fun _ => some (.ref address)) (expression := .name "xs")
    (items := (first :: rest).map Constant.int) (answer := .int (rest.foldl max first))
    (EvaluatesIn.lookup rfl) (by simpa [List.map_map] using found)
    (by simp [ScalarSet.maximum, ScalarSet.maximumFrom_ints])
  exact run.mono (by simp only [SetWork.extremum_ints, List.length_cons]; omega)
