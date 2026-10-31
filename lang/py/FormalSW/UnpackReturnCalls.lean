import lang.py.FormalSW.HeapCalls

/-! Returning execution rules for loops that unpack sequence elements into local names. -/
namespace FormalSW.PyAst.HeapCalls
open Mutable
namespace BlockReturns
variable {globals : Mutable.Globals}

/-- Acquire the sequence once and unpack each element immediately before its body. -/
theorem for_unpack
    (ordinary : ∀ expressions, iterable ≠ .call (.name "enumerate") expressions)
    (targets : Calls.targetNames expressions = some names)
    (evaluated : Evaluates (globals := globals) module env iterable heap value middle)
    (sequence : Mutable.sequence value middle = some (.ok items, middle))
    (rest : BlockReturns (globals := globals) module env
      (.unpackStepLoop names (sequenceSource value) 0 body otherwise :: following) middle answer finalHeap) :
    BlockReturns (globals := globals) module env (.forIn (.tuple expressions) iterable body otherwise :: following)
      heap answer finalHeap := by
  intro anchors stack
  have start : step (globals := globals) module anchors
      ⟨.block (.forIn (.tuple expressions) iterable body otherwise :: following) env, stack, heap⟩ =
      .next ⟨.expr iterable env, .unpackSequence names body otherwise following env :: stack, heap⟩ := by
    have notPermutations := evaluated.not_permutations
    have notCombinations := evaluated.not_combinations
    have notDictionaryValues := evaluated.not_dictionary_values
    cases iterable <;> simp_all [step]
  exact .next start ((evaluated anchors _).trans
    (.next (by simp [step, run, sequence]) (rest anchors stack)))

/-- Read the current sequence and validate the entire item before assigning its fields. -/
theorem unpack_step
    (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (item : items[position]? = some value)
    (fields : Mutable.sequence value heap = some (.ok values, heap))
    (arity : names.length = values.length)
    (rest : BlockReturns (globals := globals) module (assignNames env names values)
      (body ++ [Calls.loopContinuation body (.unpackStepLoop names source (position + 1) body otherwise)] ++ following)
      heap answer finalHeap) :
    BlockReturns (globals := globals) module env (.unpackStepLoop names source position body otherwise :: following)
      heap answer finalHeap := by
  intro anchors stack
  exact .next (by simp [step, run, sequence, item, fields, arity]) (rest anchors stack)

/-- Exhausting the sequence executes the loop's else block before the following statements. -/
theorem unpack_done
    (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (finished : items[position]? = none)
    (rest : BlockReturns (globals := globals) module env (otherwise ++ following) heap answer finalHeap) :
    BlockReturns (globals := globals) module env (.unpackStepLoop names source position body otherwise :: following)
      heap answer finalHeap := by
  intro anchors stack
  exact .next (by simp [step, run, sequence, finished]) (rest anchors stack)

end BlockReturns
end FormalSW.PyAst.HeapCalls
