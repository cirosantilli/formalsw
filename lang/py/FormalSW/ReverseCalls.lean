import lang.py.FormalSW.HeapCalls

/-! Compositional rules for fresh reverse iterators over builtin sequences. -/

namespace FormalSW.PyAst.HeapCalls
open Mutable

namespace BlockReturns

theorem for_reversed
    (evaluated : Evaluates (globals := globals) module env iterable heap value middle)
    (sequence : Mutable.reversibleSequence value middle = some (.ok items, middle))
    (rest : BlockReturns (globals := globals) module env
      (.reverseSequenceStepLoop name (sequenceSource value) ((items.length : Int) - 1) body otherwise :: following) middle answer finalHeap) :
    BlockReturns (globals := globals) module env (.forReversed name iterable body otherwise :: following)
      heap answer finalHeap := by
  intro anchors stack
  have start : step (globals := globals) module anchors ⟨.block (.forReversed name iterable body otherwise :: following) env, stack, heap⟩ =
      .next ⟨.expr iterable env, .reverseSequence name body otherwise following env :: stack, heap⟩ := by
    rfl
  exact .next start ((evaluated anchors _).trans
    (.next (by simp [step, run, sequence]) (rest anchors stack)))

/-- Read the current element, then decrement the private cursor. -/
theorem reverse_step (nonnegative : 0 ≤ position)
    (sequence : Mutable.reversibleSequence (sequenceValue source) heap = some (.ok items, heap))
    (item : items[position.toNat]? = some value)
    (rest : BlockReturns (globals := globals) module (setLocal env name value)
      (body ++ [Calls.loopContinuation body (.reverseSequenceStepLoop name source (position - 1) body otherwise)] ++ following)
      heap answer finalHeap) :
    BlockReturns (globals := globals) module env (.reverseSequenceStepLoop name source position body otherwise :: following)
      heap answer finalHeap := by
  intro anchors stack
  exact .next (by simp [step, run, sequence, Int.not_lt.mpr nonnegative, item]) (rest anchors stack)

theorem reverse_missing (nonnegative : 0 ≤ position)
    (sequence : Mutable.reversibleSequence (sequenceValue source) heap = some (.ok items, heap))
    (finished : items[position.toNat]? = none)
    (rest : BlockReturns (globals := globals) module env (otherwise ++ following) heap answer finalHeap) :
    BlockReturns (globals := globals) module env (.reverseSequenceStepLoop name source position body otherwise :: following)
      heap answer finalHeap := by
  intro anchors stack
  exact .next (by simp [step, run, sequence, Int.not_lt.mpr nonnegative, finished]) (rest anchors stack)

theorem reverse_done (finished : position < 0)
    (rest : BlockReturns (globals := globals) module env (otherwise ++ following) heap answer finalHeap) :
    BlockReturns (globals := globals) module env (.reverseSequenceStepLoop name source position body otherwise :: following)
      heap answer finalHeap := by
  intro anchors stack
  exact .next (by simp [step, finished]) (rest anchors stack)

end BlockReturns

namespace BlockContinues

theorem for_reversed
    (evaluated : Evaluates (globals := globals) module env iterable heap value middle)
    (sequence : Mutable.reversibleSequence value middle = some (.ok items, middle))
    (rest : BlockContinues (globals := globals) module env
      [.reverseSequenceStepLoop name (sequenceSource value) ((items.length : Int) - 1) body otherwise] middle finalEnv finalHeap) :
    BlockContinues (globals := globals) module env [.forReversed name iterable body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  have start : step (globals := globals) module anchors ⟨.block (.forReversed name iterable body otherwise :: following) env, stack, heap⟩ =
      .next ⟨.expr iterable env, .reverseSequence name body otherwise following env :: stack, heap⟩ := by
    rfl
  exact .next start ((evaluated anchors _).trans
    (.next (by simp [step, run, sequence]) (rest following anchors stack)))

theorem reverse_step (nonnegative : 0 ≤ position)
    (sequence : Mutable.reversibleSequence (sequenceValue source) heap = some (.ok items, heap))
    (item : items[position.toNat]? = some value)
    (rest : BlockContinues (globals := globals) module (setLocal env name value)
      (body ++ [Calls.loopContinuation body (.reverseSequenceStepLoop name source (position - 1) body otherwise)])
      heap finalEnv finalHeap) :
    BlockContinues (globals := globals) module env [.reverseSequenceStepLoop name source position body otherwise]
      heap finalEnv finalHeap := by
  intro following anchors stack
  refine .next ?_ (rest following anchors stack)
  simp [step, run, sequence, Int.not_lt.mpr nonnegative, item, List.append_assoc]

theorem reverse_missing (nonnegative : 0 ≤ position)
    (sequence : Mutable.reversibleSequence (sequenceValue source) heap = some (.ok items, heap))
    (finished : items[position.toNat]? = none)
    (rest : BlockContinues (globals := globals) module env otherwise heap finalEnv finalHeap) :
    BlockContinues (globals := globals) module env [.reverseSequenceStepLoop name source position body otherwise]
      heap finalEnv finalHeap :=
  fun following anchors stack => .next (by simp [step, run, sequence, Int.not_lt.mpr nonnegative, finished]) (rest following anchors stack)

theorem reverse_done (finished : position < 0)
    (rest : BlockContinues (globals := globals) module env otherwise heap finalEnv finalHeap) :
    BlockContinues (globals := globals) module env [.reverseSequenceStepLoop name source position body otherwise]
      heap finalEnv finalHeap :=
  fun following anchors stack => .next (by simp [step, finished]) (rest following anchors stack)

end BlockContinues

end FormalSW.PyAst.HeapCalls
