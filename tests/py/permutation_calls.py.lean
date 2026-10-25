import «.formalsw».tests.py.«permutation_calls.py.ast»
import lang.py.FormalSW.PermutationCalls

namespace tests.py.permutation_calls
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := PermutationCallsAst.module
private abbrev body : List Stmt := [.augAssign (.name "total") .add (.constant (.int 1))]

private theorem count_loop (rows : List (List SequenceSource)) (heap : Heap) (env : HeapCalls.Env)
    (acc : Int) (lookup : env "total" = some (.scalar (.int acc))) :
    ∃ finalHeap, BlockReturns program env
      [.permutationStepLoop "p" rows body [], .return (.name "total")]
      heap (.scalar (.int (acc + rows.length))) finalHeap := by
  induction rows generalizing heap env acc with
  | nil =>
      refine ⟨heap, BlockReturns.permutation_done ?_⟩
      simpa using BlockReturns.return_value (Evaluates.lookup lookup)
  | cons row remaining ih =>
      obtain ⟨tuple, middle, allocated⟩ := tuple_allocates (row.map sequenceValue) heap
      let bound := setLocal env "p" tuple
      obtain ⟨finalHeap, rest⟩ := ih middle (setLocal bound "total" (.scalar (.int (acc + 1)))) (acc + 1) rfl
      refine ⟨finalHeap, BlockReturns.permutation_step allocated ?_⟩
      apply BlockReturns.augAssign (left := .scalar (.int acc))
        (by simpa [setLocal] using lookup) Evaluates.constant
        (middle := middle) (afterOperation := middle) (value := .scalar (.int (acc + 1))) rfl
      simpa [body, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        Int.add_assoc, Int.add_comm, Int.add_left_comm, bound] using rest

theorem count.result (heap : Heap) (address : Nat) (items : List Mutable.Value)
    (found : heap[address]? = some (.list items)) :
    ∃ finalHeap, ReturnsValue program "count" [.ref address] heap
      (.scalar (.int (Math.factorial items.length))) finalHeap := by
  let rows := (Permutations.rows items.length items).map (List.map sequenceSource)
  let env := setLocal (argumentEnv
    [{ name := "xs", annotation := some (.subscript (.name "list") (.name "int")) }]
    [.ref address]) "total" (.scalar (.int 0))
  obtain ⟨finalHeap, loop⟩ := count_loop rows heap env 0 rfl
  refine ⟨finalHeap, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign Evaluates.constant
  apply BlockReturns.for_permutations (.cons (Evaluates.lookup rfl) (.cons Evaluates.constant .nil))
    (permutationRows_list heap address items found)
  simpa [rows, Permutations.rows_full_length] using loop

theorem count.«Returns» (heap : Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "count" [.ref address] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  obtain ⟨finalHeap, result⟩ := count.result heap address _ found
  exact result.returns

theorem count.«Supported» (heap : Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "count" [.ref address] heap).Supported :=
  (count.«Returns» heap address valid typed).supported

end tests.py.permutation_calls
