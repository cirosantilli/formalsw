import lang.py.FormalSW.HeapRuntimeCostSetComprehensions
import lang.py.FormalSW.HeapRuntimeCostSets

open FormalSW.PyAst HeapCalls HeapCalls.Runtime

private def emptyModule : Module := { body := [] }

/-- An empty range skips even undefined filter and element expressions, but
still charges acquisition, allocation and iterator exhaustion. -/
example (env : HeapCalls.Env) (heap : Mutable.Heap) :
    EvaluatesIn .word emptyModule env
      (.setComp (.name "missing") [(.name "x", .call (.name "range") [.constant (.int 0)],
        [.name "undefined_filter"])]) heap 13 (.ref heap.length) (heap ++ [.set []]) := by
  apply EvaluatesIn.set_comp_range (ca := 2) (work := 3) (cb := 4)
    (values := [.scalar (.int 0)])
    (ArgumentsIn.cons EvaluatesIn.constant ArgumentsIn.nil) rfl rfl
  exact BlockContinuesIn.range_done rfl BlockContinuesIn.nil

/-- Duplicate keys pay for search even though the stored set is unchanged. -/
example (env : HeapCalls.Env) :
    BlockContinuesIn .word emptyModule env [.comprehensionAdd 0 (.constant (.int 10))]
      [.set [.int 10]] 23 env [.set [.int 10]] :=
  BlockContinuesIn.comprehension_add (items := [.int 10]) EvaluatesIn.constant rfl

private def program : Module :=
  { body := [.functionDef "emit" [⟨"s", none, none⟩] none
    [.expr (.call (.attribute (.name "s") "add") [.constant (.int 2)]),
      .return (.constant (.int 1))]] }

/-- Insertion sees the set after evaluating the element, including mutations
performed by that expression's helper call. -/
example (env : HeapCalls.Env) (get : env "s" = some (.ref 0)) :
    BlockContinuesIn .word program env
      [.comprehensionAdd 0 (.call (.name "emit") [.name "s"])]
      [.set [.int 10]] 65 env [.set [.int 10, .int 2, .int 1]] := by
  let entry := functionEnv [⟨"s", none, none⟩]
    [.expr (.call (.attribute (.name "s") "add") [.constant (.int 2)]),
      .return (.constant (.int 1))] [.ref 0] []
  have added : EvaluatesIn .word program entry
      (.call (.attribute (.name "s") "add") [.constant (.int 2)])
      [.set [.int 10]] 24 (.scalar .none) [.set [.int 10, .int 2]] :=
    EvaluatesIn.set_add (address := 0) (old := [.int 10]) (current := [.int 10])
      (EvaluatesIn.lookup rfl) rfl EvaluatesIn.constant rfl
  have helper : ReturnsIn .word program "emit" [.ref 0] [.set [.int 10]] 31
      (.scalar (.int 1)) [.set [.int 10, .int 2]] := by
    apply BlockReturnsIn.function (args := [⟨"s", none, none⟩]) (budget := 28) rfl rfl
    exact (BlockContinuesIn.discard added).returns (BlockReturnsIn.return_value EvaluatesIn.constant)
  exact BlockContinuesIn.comprehension_add (items := [.int 10, .int 2])
    (EvaluatesIn.call_single (EvaluatesIn.lookup get) helper) rfl

/-- Fixed arithmetic retains string-key work, and bit arithmetic retains
integer-key widths. Unsupported object-key insertion has no fallback price. -/
example : SetWork.insert .collisionChain .word [.string "A"] (.string "ABCDEFGH") >
    SetWork.insert .collisionChain .word [.string "A"] (.string "B") := by decide
example : SetWork.insert .collisionChain .bits [.int 1] (.int (2^100)) >
    SetWork.insert .collisionChain .word [.int 1] (.int (2^100)) := by decide
example : operation .word [.set []] (.add 0) [.ref 1] = none := rfl
