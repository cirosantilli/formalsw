import lang.py.FormalSW.PermutationCalls

/-! Fresh combination loops reuse tuple allocation and loop control from positional selections. -/
namespace FormalSW.PyAst.HeapCalls
variable {globals : Mutable.Globals}

theorem combinationRows_list (heap : Heap) (address count : Nat) (items : List Value)
    (found : heap[address]? = some (.list items)) :
    combinationRows [.ref address, .scalar (.int count)] heap =
      some (.ok ((Combinations.rows count items).map (List.map sequenceSource)), heap) := by
  simp [combinationRows, Combinations.acquire_list heap address count items found]

theorem BlockReturns.for_combinations
    (arguments : Evaluates.Arguments (globals := globals) module env expressions heap values middle)
    (captured : combinationRows values middle = some (.ok rows, middle))
    (rest : BlockReturns (globals := globals) module env
      (.permutationStepLoop (comprehensionTargetName target) rows
        (comprehensionTargetBody target body) otherwise :: following) middle answer finalHeap) :
    BlockReturns (globals := globals) module env
      (.forIn target (.combinationsIterable expressions) body otherwise :: following) heap answer finalHeap := by
  intro anchors stack
  exact .next rfl ((Evaluates.arguments_reach arguments _ [] anchors stack).trans
    (.next (by simp [step, run, captured]) (rest anchors stack)))

theorem BlockContinues.for_combinations
    (arguments : Evaluates.Arguments (globals := globals) module env expressions heap values middle)
    (captured : combinationRows values middle = some (.ok rows, middle))
    (executed : BlockContinues (globals := globals) module env
      [.permutationStepLoop (comprehensionTargetName target) rows
        (comprehensionTargetBody target body) otherwise] middle finalEnv finalHeap) :
    BlockContinues (globals := globals) module env
      [.forIn target (.combinationsIterable expressions) body otherwise] heap finalEnv finalHeap := by
  intro following anchors stack
  exact .next rfl ((Evaluates.arguments_reach arguments _ [] anchors stack).trans
    (.next (by simp [step, run, captured]) (executed following anchors stack)))

end FormalSW.PyAst.HeapCalls
