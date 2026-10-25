import «.formalsw».tests.py.«set_comprehensions.py.ast»
import FormalSW

namespace tests.py.set_comprehensions
open FormalSW.PyAst HeapCalls
private abbrev program := SetComprehensionsAst.module
private abbrev values (items : List Int) : List Mutable.Value :=
  items.map (fun value => .scalar (.int value))
private abbrev body (address : Nat) : List Stmt :=
  [.comprehensionAdd address (.name "value")]

theorem loop_result (heap : Mutable.Heap) (address : Nat) (items remaining : List Int)
    (found : heap[address]? = some (.list (values items))) (position : Nat)
    (suffix : items.drop position = remaining) (collected : List Constant) (env : HeapCalls.Env) :
    ∃ finalEnv, BlockContinues program env
      [.sequenceStepLoop "value" (.ref address) position (body heap.length) []]
      (heap ++ [.set collected]) finalEnv
      (heap ++ [.set (remaining.foldl (fun soFar item => ScalarSet.insert soFar (.int item)) collected)]) := by
  have inside : address < heap.length := by
    by_cases inside : address < heap.length
    · exact inside
    · have missing := List.getElem?_eq_none (Nat.le_of_not_gt inside)
      simp [missing] at found
  have sequence (collected : List Constant) :
      Mutable.sequence (.ref address) (heap ++ [.set collected]) =
        some (.ok (values items), heap ++ [.set collected]) := by
    simp [Mutable.sequence, List.getElem?_append_left inside, found]
  induction remaining generalizing position collected env with
  | nil =>
      refine ⟨env, BlockContinues.sequence_done (source := .ref address) (sequence collected) ?_ .nil⟩
      have missing : items[position]? = none := by
        simpa [suffix] using (List.head?_drop (l := items) (i := position)).symm
      simp [values, missing]
  | cons head tail ih =>
      let boundEnv := setLocal env "value" (.scalar (.int head))
      have emitted : BlockContinues program boundEnv (body heap.length)
          (heap ++ [.set collected]) boundEnv
          (heap ++ [.set (ScalarSet.insert collected (.int head))]) := by
        have write := BlockContinues.comprehension_add
          (globals := []) (module := program) (env := boundEnv) (address := heap.length)
          (heap := heap ++ [.set collected]) (Evaluates.lookup (name := "value") rfl)
          (by simp : (heap ++ [.set collected])[heap.length]? = some (.set collected))
        simpa [body] using write
      obtain ⟨finalEnv, rest⟩ := ih (position + 1)
        (by simp [List.drop_add_one_eq_tail_drop, suffix])
        (ScalarSet.insert collected (.int head)) boundEnv
      refine ⟨finalEnv, ?_⟩
      have item : items[position]? = some head := by
        simpa [suffix] using (List.head?_drop (l := items) (i := position)).symm
      apply BlockContinues.sequence_step (source := .ref address)
        (value := .scalar (.int head)) (sequence collected) (by simp [values, item])
      simpa [body, Calls.loopContinuation, Calls.loopControl, boundEnv] using emitted.append rest

theorem distinct.result (heap : Mutable.Heap) (address : Nat) (items : List Int)
    (found : heap[address]? = some (.list (values items))) :
    ReturnsValue program "distinct" [.ref address] heap (.ref heap.length)
      (heap ++ [.set (items.foldl (fun soFar item => ScalarSet.insert soFar (.int item)) [])]) := by
  let env := HeapCalls.argumentEnv [⟨"values", some (.subscript (.name "list") (.name "int")), none⟩] [.ref address]
  obtain ⟨finalEnv, executed⟩ := loop_result heap address items items found 0 rfl []
    (comprehensionTargetsEnv env [(.name "value", .name "values", [])])
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.set_comp_sequence (value := .ref address) (middle := heap)
    (items := values items) (finalEnv := finalEnv)
    (by intro expressions impossible; cases impossible)
    (by intro expressions impossible; cases impossible)
    (by intro expressions impossible; cases impossible)
  · exact Evaluates.lookup rfl
  · simp [Mutable.sequence, found]
  · exact executed

theorem distinct.«Returns» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "distinct" [.ref address] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (distinct.result heap address items found).returns

theorem distinct.«Supported» (heap : Mutable.Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "distinct" [.ref address] heap).Supported :=
  (distinct.«Returns» heap address valid typed).supported

end tests.py.set_comprehensions
