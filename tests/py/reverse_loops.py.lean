import «.formalsw».tests.py.«reverse_loops.py.ast»
import FormalSW

namespace tests.py.reverse_loops
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := ReverseLoopsAst.module
private def body : List Stmt := [.augAssign (.name "total") .add (.constant (.int 1))]

private theorem loop_result (remaining : Nat) (items : List Mutable.Value) (address : Nat)
    (heap : Mutable.Heap) (found : heap[address]? = some (.list items))
    (bound : remaining ≤ items.length) (env : Mutable.Env) (total : Int)
    (counter : env "total" = some (.scalar (.int total))) :
    BlockReturns program env
      [.reverseSequenceStepLoop "x" (.ref address) ((remaining : Int) - 1) body [], .return (.name "total")]
      heap (.scalar (.int (total + remaining))) heap := by
  induction remaining generalizing env total with
  | zero =>
      apply BlockReturns.reverse_done (by decide)
      simpa using BlockReturns.return_value (Evaluates.lookup counter)
  | succ remaining ih =>
      have index : remaining < items.length := by omega
      simp only [Int.natCast_add, Int.natCast_one, Int.add_sub_cancel]
      apply BlockReturns.reverse_step (by omega)
        (by simp [sequenceValue, Mutable.reversibleSequence, Mutable.sequence, found])
        (items := items) (value := items[remaining])
        (by simp)
      change BlockReturns program (setLocal env "x" items[remaining])
        (.augAssign (.name "total") .add (.constant (.int 1)) ::
          [.reverseSequenceStepLoop "x" (.ref address) ((remaining : Int) - 1) body [], .return (.name "total")])
        heap (.scalar (.int (total + (remaining + 1)))) heap
      apply BlockReturns.augAssign (left := .scalar (.int total))
        (value := .scalar (.int (total + 1))) (afterOperation := heap)
        (by simpa [setLocal] using counter) Evaluates.constant
        (by simp [inplace, Mutable.binary, scalarBinary])
      simpa [Int.add_assoc, Int.add_comm, Int.add_left_comm] using
        ih (by omega) (setLocal (setLocal env "x" items[remaining]) "total" (.scalar (.int (total + 1))))
          (total + 1) (by simp [setLocal])

theorem count.result (heap : Mutable.Heap) (address : Nat) (items : List Mutable.Value)
    (found : heap[address]? = some (.list items)) :
    ReturnsValue program "count" [.ref address] heap (.scalar (.int items.length)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign Evaluates.constant
  apply BlockReturns.for_reversed (items := items) (Evaluates.lookup rfl)
    (by simp [Mutable.reversibleSequence, Mutable.sequence, found])
  simpa [sequenceSource] using loop_result items.length items address heap found (by omega) _ 0 rfl

theorem count.«Returns» (heap : Mutable.Heap) (xs : Nat)
    (_valid : Mutable.Heap.Valid heap) (typed : Mutable.Value.HasType heap (.ref xs) "list[int]") :
    (HeapCalls.call program "count" [.ref xs] heap).Returns := by
  obtain ⟨items, found, _⟩ := typed
  exact (count.result heap xs items found).returns

theorem count.«Supported» (heap : Mutable.Heap) (xs : Nat)
    (valid : Mutable.Heap.Valid heap) (typed : Mutable.Value.HasType heap (.ref xs) "list[int]") :
    (HeapCalls.call program "count" [.ref xs] heap).Supported :=
  (count.«Returns» heap xs valid typed).supported

end tests.py.reverse_loops
