import lang.py.FormalSW.HeapRuntimeCostComprehensions
import lang.py.FormalSW.HeapRuntimeInputs

open FormalSW.PyAst HeapCalls HeapCalls.Runtime
private def program : Module := { body := [] }

example : NestedIntList.heap [[1, 2], [], [-5]] =
    [.list [.ref 1, .ref 2, .ref 3], .list [.scalar (.int 1), .scalar (.int 2)],
      .list [], .list [.scalar (.int (-5))]] := rfl
example : NestedIntList.size [[], [], []] = 3 := rfl
example : NestedIntList.size [[1, 2], [], [-5]] = 6 := rfl

/-- An exhausted range still allocates the empty result and checks its guard. -/
example : EvaluatesIn .word program (fun _ => none)
    (.listComp (.name "i") [("i", .call (.name "range") [.constant (.int 0)], [])])
    [] 13 (.ref 0) [.list []] := by
  apply EvaluatesIn.list_comp_range (work := 3) (cb := 4) (values := [.scalar (.int 0)])
    (start := 0) (stop := 0) (stride := 1)
    (ArgumentsIn.cons EvaluatesIn.constant ArgumentsIn.nil) rfl rfl
  exact BlockContinuesIn.range_done rfl BlockContinuesIn.nil

/-- Mutating the same list during element evaluation retains both writes. -/
example : BlockContinuesIn .word program (fun _ => some (.ref 0))
    [.comprehensionAppend 0 (.call (.attribute (.name "out") "append") [.constant (.int 4)])]
    [.list []] 16 (fun _ => some (.ref 0)) [.list [.scalar (.int 4), .scalar .none]] := by
  have mutated : EvaluatesIn .word program (fun _ => some (.ref 0))
      (.call (.attribute (.name "out") "append") [.constant (.int 4)]) [.list []]
      9 (.scalar .none) [.list [.scalar (.int 4)]] :=
    EvaluatesIn.append (address := 0) (old := []) (current := [])
      (EvaluatesIn.lookup rfl) rfl EvaluatesIn.constant rfl
  exact BlockContinuesIn.comprehension_append (address := 0) (items := [.scalar (.int 4)]) mutated rfl

/-- Zip work depends on its arity, not the product of sequence lengths. -/
example : zipIteration .word [.list [], .list [.scalar (.int 5)], .tuple []]
    [.ref 0, .ref 1, .ref 2] 0 = some 20 := rfl
example : zipIteration .word [.dict []] [.ref 0] 0 = none := rfl
example : operation .word [.dict []]
    (.comprehensionTargets (.name "x") [(.name "x", .zipIterable [.name "items"], [])] (fun _ => none))
    [.ref 0] = none := rfl

/-- A single zip iteration allocates its tuple, then pays for exhaustion. -/
example : BlockContinuesIn .word program (fun _ => none)
    [.zipStepLoop "row" [.ref 0, .ref 1, .ref 2] 0 [] []]
    [.list [.scalar (.int 1)], .list [.scalar (.int 2)], .list [.scalar (.int 3)]] 40
    (setLocal (fun _ => none) "row" (.ref 3))
    [.list [.scalar (.int 1)], .list [.scalar (.int 2)], .list [.scalar (.int 3)],
      .tuple [.scalar (.int 1), .scalar (.int 2), .scalar (.int 3)]] := by
  apply BlockContinuesIn.zip_step (work := 20) (budget := 20)
    (fields := [.scalar (.int 1), .scalar (.int 2), .scalar (.int 3)]) rfl rfl rfl
  exact BlockContinuesIn.zip_done (work := 20) rfl rfl BlockContinuesIn.nil
