import lang.py.FormalSW.HeapRuntimeCostComprehensions
import lang.py.FormalSW.HeapRuntimeInputs
import lang.py.FormalSW.HeapRuntimeCostSetup
import lang.py.FormalSW.HeapRuntimeCostListLoops

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

/-- An exhausted reverse range still evaluates all three negative bounds. -/
example (heap : Heap) : BlockReturnsIn .word program (fun _ => none)
    [.forIn (.name "i") (.call (.name "range")
      [.unaryOp .uSub (.constant (.int 1)), .unaryOp .uSub (.constant (.int 1)),
       .unaryOp .uSub (.constant (.int 1))]) [] [], .return (.constant (.int 7))]
    heap 29 (.scalar (.int 7)) heap := by
  apply BlockReturnsIn.for_range_triple (cost := 6)
    (EvaluatesIn.negate_int EvaluatesIn.constant)
    (EvaluatesIn.negate_int EvaluatesIn.constant)
    (EvaluatesIn.negate_int EvaluatesIn.constant) (by decide)
  exact (BlockContinuesIn.range_done (module := program) (name := "i")
    (next := -1) (stop := -1) (stride := -1) (body := []) (otherwise := [])
    rfl BlockContinuesIn.nil).returns (BlockReturnsIn.return_value EvaluatesIn.constant)

example (length : Nat) : SequenceWork.slice .word length (.scalar .none) (.scalar .none) (.scalar .none) =
    some (6*length+201) := SequenceWork.slice_full length

/-- An empty slice creates the list which the loop subsequently iterates. -/
example : BlockReturnsIn .word program (fun _ => some (.ref 0))
    [.forIn (.name "x") (.subscript (.name "rows") (.slice (some (.constant (.int 1))) none none)) [] [],
      .return (.constant (.int 7))]
    [.list []] 226 (.scalar (.int 7)) [.list [], .list []] := by
  have sliced : EvaluatesIn .word program (fun _ => some (.ref 0))
      (.subscript (.name "rows") (.slice (some (.constant (.int 1))) none none)) [.list []]
      217 (.ref 1) [.list [], .list []] := by
    exact EvaluatesIn.list_suffix_word (items := []) (EvaluatesIn.lookup rfl) rfl 1
  apply BlockReturnsIn.for_list_subscript (budget := 7) sliced rfl
  exact BlockReturnsIn.list_done rfl rfl (BlockReturnsIn.return_value EvaluatesIn.constant)

/-- The out-of-range read is not evaluated when the list condition is empty. -/
example : EvaluatesIn .word program (fun _ => some (.ref 0))
    (.ifExp (.name "acc") (.subscript (.name "acc") (.constant (.int 0))) (.constant (.int 7)))
    [.list []] 4 (.scalar (.int 7)) [.list []] :=
  EvaluatesIn.list_conditional (flag := false) (EvaluatesIn.lookup rfl) rfl rfl EvaluatesIn.constant
