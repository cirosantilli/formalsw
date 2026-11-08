import lang.py.FormalSW.HeapRuntimeCostSumGenerators
import lang.py.FormalSW.ComprehensionCalls

/-! Enumerating a live list retains its receiver, assigns the index before the
item, and charges both index operations under the word arithmetic model. -/
namespace FormalSW.PyAst.HeapCalls.Runtime
open PrimitiveWork
variable {globals : Mutable.Globals}

namespace BlockContinuesIn

/-- Read the current list at this iteration, then bind both targets in Python
order. The continuation may mutate the list or any other heap object. -/
theorem list_enumerate_step (found : heap[address]? = some (.list items))
    (item : items[position]? = some value)
    (rest : BlockContinuesIn (globals := globals) .word module
      (setLocal (setLocal env index (.scalar (.int counter))) name value)
      (body ++ [Calls.loopContinuation body
        (.enumerateStepLoop index name (.ref address) (position + 1) (counter + 1) body otherwise)])
      heap budget finalEnv finalHeap) :
    BlockContinuesIn (globals := globals) .word module env
      [.enumerateStepLoop index name (.ref address) position counter body otherwise]
      heap (budget + 7) finalEnv finalHeap := by
  intro following anchors stack
  have initial : Reaches (globals := globals) .word module anchors
      ⟨.block ([.enumerateStepLoop index name (.ref address) position counter body otherwise] ++ following)
        env, stack, heap⟩ 7
      ⟨.block ((body ++ [Calls.loopContinuation body
        (.enumerateStepLoop index name (.ref address) (position + 1) (counter + 1) body otherwise)]) ++ following)
        (setLocal (setLocal env index (.scalar (.int counter))) name value), stack, heap⟩ :=
    advance (by simp [step, run, sequenceValue, Mutable.sequence, found, item, List.append_assoc])
      (by simp [charge, found, integer]) rfl
  exact (initial.trans (rest following anchors stack)).mono (by omega)

/-- Exhaustion uses the current list length and executes the source `else`
block without changing either enumeration target. -/
theorem list_enumerate_done (found : heap[address]? = some (.list items))
    (finished : items[position]? = none)
    (rest : BlockContinuesIn (globals := globals) .word module env otherwise heap budget finalEnv finalHeap) :
    BlockContinuesIn (globals := globals) .word module env
      [.enumerateStepLoop index name (.ref address) position counter body otherwise]
      heap (budget + 7) finalEnv finalHeap := by
  intro following anchors stack
  have initial : Reaches (globals := globals) .word module anchors
      ⟨.block ([.enumerateStepLoop index name (.ref address) position counter body otherwise] ++ following)
        env, stack, heap⟩ 7
      ⟨.block (otherwise ++ following) env, stack, heap⟩ :=
    advance (by simp [step, run, sequenceValue, Mutable.sequence, found, finished])
      (by simp [charge, found, integer]) rfl
  exact (initial.trans (rest following anchors stack)).mono (by omega)

/-- Evaluate the iterable before the explicit signed start. The list is read
from the heap after both evaluations, allowing effects in either expression. -/
theorem for_list_enumerate_start
    (iterable : EvaluatesIn (globals := globals) .word module env expression heap ca (.ref address) middle)
    (start : EvaluatesIn (globals := globals) .word module env startExpression middle cb
      (.scalar (.int counter)) afterStart)
    (found : afterStart[address]? = some (.list items))
    (rest : BlockContinuesIn (globals := globals) .word module env
      [.enumerateStepLoop index name (.ref address) 0 counter body otherwise]
      afterStart budget finalEnv finalHeap) :
    BlockContinuesIn (globals := globals) .word module env
      [.forIn (.tuple [.name index, .name name])
        (.call (.name "enumerate") [expression, startExpression]) body otherwise]
      heap (ca + cb + budget + 7) finalEnv finalHeap := by
  intro following anchors stack
  have initial : Reaches (globals := globals) .word module anchors
      ⟨.block ([.forIn (.tuple [.name index, .name name])
        (.call (.name "enumerate") [expression, startExpression]) body otherwise] ++ following)
        env, stack, heap⟩ 3
      ⟨.expr expression env,
        .enumerateSource index name startExpression body otherwise following env :: stack, heap⟩ :=
    advance rfl rfl rfl
  have ready : Reaches (globals := globals) .word module anchors
      ⟨.value (.ref address),
        .enumerateSource index name startExpression body otherwise following env :: stack, middle⟩ 1
      ⟨.expr startExpression env,
        .enumerateStart index name (.ref address) body otherwise following env :: stack, middle⟩ :=
    advance rfl rfl rfl
  have enter : Reaches (globals := globals) .word module anchors
      ⟨.value (.scalar (.int counter)),
        .enumerateStart index name (.ref address) body otherwise following env :: stack, afterStart⟩ 3
      ⟨.block ([.enumerateStepLoop index name (.ref address) 0 counter body otherwise] ++ following)
        env, stack, afterStart⟩ :=
    advance (by simp [step, run, enumerateStart, Mutable.sequence, found, sequenceSource])
      (by simp [charge, found, scalarNumber, integer]) rfl
  exact (((((initial.trans (iterable anchors _)).trans ready).trans (start anchors _)).trans enter).trans
    (rest following anchors stack)).mono (by omega)

end BlockContinuesIn

/-- Summation of an indexed expression over an unchanged list. Each item has
its own tariff, independent of the signed counter under fixed arithmetic. -/
theorem sum_enumerate_loop_costs {α : Type} {values : List α} {encode : α → Value}
    {number : Int → α → Int}
    (remaining : List α) (position : Nat) (counter : Int) (itemCost : α → Nat)
    (distinct : index ≠ name)
    (privateIndex : index ≠ sumAccumulator) (privateName : name ≠ sumAccumulator)
    (found : heap[address]? = some (.list (values.map encode)))
    (evaluated : ∀ env counter item,
      env index = some (.scalar (.int counter)) → env name = some (encode item) →
      EvaluatesIn (globals := globals) .word module env element heap (itemCost item)
        (.scalar (.int (number counter item))) heap)
    (suffix : values.drop position = remaining)
    (accumulator : env sumAccumulator = some (.scalar (.int initial))) :
    BlockReturnsIn (globals := globals) .word module env
      [.enumerateStepLoop index name (.ref address) position counter (sumBody element []) [],
        .return (.name sumAccumulator)] heap
      ((remaining.map (fun item => itemCost item + 14)).sum + 9)
      (.scalar (.int (indexedSum number counter initial remaining))) heap := by
  induction remaining generalizing position counter env initial with
  | nil =>
      have missing : values[position]? = none := by
        simpa [suffix] using (List.head?_drop (l := values) (i := position)).symm
      intro anchors stack
      have head : Reaches (globals := globals) .word module anchors
          ⟨.block [.enumerateStepLoop index name (.ref address) position counter (sumBody element []) [],
            .return (.name sumAccumulator)] env, stack, heap⟩ 7
          ⟨.block [.return (.name sumAccumulator)] env, stack, heap⟩ :=
        advance (by simp [step, run, sequenceValue, Mutable.sequence, found, missing])
          (by simp [charge, found, integer]) rfl
      exact head.trans (BlockReturnsIn.return_value (EvaluatesIn.lookup accumulator) anchors stack)
  | cons item rest ih =>
      have itemFound : values[position]? = some item := by
        simpa [suffix] using (List.head?_drop (l := values) (i := position)).symm
      let itemEnv := setLocal (setLocal env index (.scalar (.int counter))) name (encode item)
      have itemRun := evaluated itemEnv counter item
        (by simp [itemEnv, setLocal, distinct]) (by simp [itemEnv, setLocal])
      have addition : EvaluatesIn (globals := globals) .word module itemEnv
          (.binOp (.name sumAccumulator) .add element) heap (itemCost item + 5)
          (.scalar (.int (initial + number counter item))) heap := by
        have run := EvaluatesIn.binary (op := .add) (av := .int initial)
          (bv := .int (number counter item)) (work := 1)
          (EvaluatesIn.lookup (name := sumAccumulator)
            (by simpa [itemEnv, setLocal, Ne.symm privateIndex, Ne.symm privateName] using accumulator))
          itemRun rfl rfl
        exact run.mono (by omega)
      have tail := ih (position + 1) (counter + 1) (initial := initial + number counter item)
        (env := setLocal itemEnv sumAccumulator (.scalar (.int (initial + number counter item))))
        (by simp [List.drop_add_one_eq_tail_drop, suffix]) (by simp [setLocal])
      intro anchors stack
      have head : Reaches (globals := globals) .word module anchors
          ⟨.block [.enumerateStepLoop index name (.ref address) position counter (sumBody element []) [],
            .return (.name sumAccumulator)] env, stack, heap⟩ 7
          ⟨.block (sumBody element [] ++
            [.enumerateStepLoop index name (.ref address) (position + 1) (counter + 1) (sumBody element []) [],
              .return (.name sumAccumulator)]) itemEnv, stack, heap⟩ :=
        advance (by simp [step, run, sequenceValue, Mutable.sequence, found, itemFound, itemEnv,
          sumBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt])
          (by simp [charge, found, integer]) rfl
      exact (head.trans (BlockReturnsIn.assign addition tail anchors stack)).mono (by simp; omega)

end FormalSW.PyAst.HeapCalls.Runtime
