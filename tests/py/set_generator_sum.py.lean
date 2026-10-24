import «.formalsw».tests.py.«set_generator_sum.py.ast»
import lang.py.FormalSW.SetSumCalls

namespace tests.py.set_generator_sum
open FormalSW.PyAst
open HeapCalls
private abbrev program := SetGeneratorSumAst.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
private abbrev body := sumBody (.constant (.int 1)) []

theorem count.result (heap : Mutable.Heap) (address : Nat) (items : List Constant)
    (found : heap[address]? = some (.set items)) :
    SetCalls.ReturnsValue program "count" [.ref address] heap
      (number ((items.map (fun _ => (1 : Int))).sum)) heap := by
  apply SetCalls.BlockReturns.function rfl rfl
  apply SetCalls.BlockReturns.return_value
  apply SetCalls.Evaluates.sum_generator_set (by intros; simp)
    (HeapCalls.Evaluates.lookup rfl) found HeapCalls.Evaluates.constant rfl
  intro choices anchors stack used
  let definition := (findFunctionIn program.body "count").getD ([], [])
  let initial := functionEnv definition.1 definition.2 [.ref address] []
  let generator := setLocal (comprehensionEnv initial [("value", .name "values", [])])
    sumAccumulator (number 0)
  have iterate (env : HeapCalls.Env) (total : Int) (item : Constant)
      (_valid : True) (_member : item ∈ items)
      (accumulator : env sumAccumulator = some (number total)) :
      ∃ updated, HeapCalls.BlockContinues program
        (setLocal env "value" (.scalar item)) body heap updated heap ∧ True ∧
        updated sumAccumulator = some (number (total + 1)) := by
    let bound := setLocal env "value" (.scalar item)
    let updated := setLocal bound sumAccumulator (number (total + 1))
    refine ⟨updated, ?_, trivial, by simp [updated, setLocal]⟩
    apply HeapCalls.BlockContinues.assign (value := number (total + 1)) (finalHeap := heap)
    apply HeapCalls.Evaluates.binary (av := number total) (bv := number 1)
      (middle := heap) (afterRight := heap)
    · exact HeapCalls.Evaluates.lookup
        (by simpa [bound, setLocal, sumAccumulator] using accumulator)
    · exact HeapCalls.Evaluates.constant
    · rfl
  have result := SetCalls.sum_map_loop choices program heap address items items found
    (fun _ member => member) "value" body (fun _ => 1) (fun _ => True) rfl
    iterate 0 generator trivial (by simp [generator, setLocal]) anchors stack used
  simpa only [Int.zero_add] using result

theorem count.«Returns» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "set[int]") :
    (SetCalls.call program "count" [.ref address] heap).Returns := by
  obtain ⟨items, found, _⟩ := typed
  intro choices
  exact ⟨_, [], heap, heap.length, (count.result heap address items found).finishes choices⟩

theorem count.«Supported» (heap : Mutable.Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "set[int]") :
    (SetCalls.call program "count" [.ref address] heap).Supported := by
  intro choices
  exact (count.«Returns» heap address valid typed choices).supported

end tests.py.set_generator_sum
