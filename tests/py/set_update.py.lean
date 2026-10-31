import «.formalsw».tests.py.«set_update.py.ast»
import lang.py.FormalSW.SetUpdateCalls
import lang.py.FormalSW.SetChoiceCalls

namespace tests.py.set_update
open FormalSW.PyAst HeapCalls
private abbrev program := SetUpdateAst.module
private abbrev body : List Stmt := [.expr (.call (.attribute (.name "target") "add") [.name "value"])]

private theorem set_same (heap : Heap) (address : Nat) (object : Mutable.Object)
    (found : heap[address]? = some object) : heap.set address object = heap := by
  obtain ⟨inside, entry⟩ := List.getElem?_eq_some_iff.mp found
  rw [← entry, List.set_getElem_self inside]

private theorem set_twice (heap : Heap) (address : Nat) (first second : Mutable.Object) :
    (heap.set address first).set address second = heap.set address second := by
  induction heap generalizing address with
  | nil => simp
  | cons item rest ih => cases address <;> simp [List.set, ih]

private theorem naive_loop (remaining : List Constant) (heap : Heap) (address source position : Nat)
    (old items : List Constant) (env : HeapCalls.Env)
    (destination : heap[address]? = some (.set old))
    (input : heap[source]? = some (.list (items.map Mutable.Value.scalar)))
    (suffix : items.drop position = remaining) (target : env "target" = some (.ref address)) :
    BlockReturns program env [.sequenceStepLoop "value" (.ref source) position body [], .return (.name "target")]
      heap (.ref address) (heap.set address (.set (remaining.foldl ScalarSet.insert old))) := by
  have distinct : address ≠ source := by
    intro equal
    subst source
    simp [destination] at input
  induction remaining generalizing heap position old env with
  | nil =>
    rw [List.foldl_nil, set_same heap address (.set old) destination]
    apply BlockReturns.sequence_done (items := items.map Mutable.Value.scalar)
      (by simp [sequenceValue, Mutable.sequence, input])
    · have atHead := congrArg (fun xs : List Constant => xs[0]?) suffix
      simpa using congrArg (Option.map Mutable.Value.scalar) atHead
    · exact BlockReturns.return_value (Evaluates.lookup target)
  | cons item rest ih =>
    let bound := setLocal env "value" (.scalar item)
    let inserted := ScalarSet.insert old item
    let middle := heap.set address (.set inserted)
    have selected : (items.map Mutable.Value.scalar)[position]? = some (.scalar item) := by
      have atHead := congrArg (fun xs : List Constant => xs[0]?) suffix
      simpa using congrArg (Option.map Mutable.Value.scalar) atHead
    have nextDestination : middle[address]? = some (.set inserted) := by
      simp [middle, (List.getElem?_eq_some_iff.mp destination).1]
    have nextInput : middle[source]? = some (.list (items.map Mutable.Value.scalar)) := by
      simpa [middle, List.getElem?_set, distinct, Ne.symm distinct] using input
    have nextSuffix : items.drop (position + 1) = rest := by
      simpa only [List.tail_drop, List.tail_cons] using congrArg List.tail suffix
    have nextTarget : bound "target" = some (.ref address) := by simp [bound, setLocal, target]
    have continued := ih middle (position + 1) inserted bound nextDestination nextInput nextSuffix nextTarget
    apply BlockReturns.sequence_step (items := items.map Mutable.Value.scalar) (value := .scalar item)
      (by simp [sequenceValue, Mutable.sequence, input]) selected
    have appended := BlockReturns.discard
      (Evaluates.add (Evaluates.lookup nextTarget) destination
        (Evaluates.lookup (show bound "value" = some (.scalar item) by simp [bound, setLocal])) destination)
      continued
    simpa only [body, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, Bool.false_eq_true,
      if_false, List.nil_append, List.cons_append, List.foldl_cons, middle, inserted, set_twice] using appended

private theorem naive_result (heap : Heap) (address source : Nat) (old items : List Constant)
    (destination : heap[address]? = some (.set old))
    (input : heap[source]? = some (.list (items.map Mutable.Value.scalar))) :
    ReturnsValue program "naive" [.ref address, .ref source] heap (.ref address)
      (heap.set address (.set (items.foldl ScalarSet.insert old))) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.for_sequence (items := items.map Mutable.Value.scalar) (by intro expressions impossible; cases impossible)
    (Evaluates.lookup rfl) (by simp [Mutable.sequence, input])
  exact naive_loop items heap address source 0 old items _ destination input rfl rfl

private theorem merge_result (heap : Heap) (address source : Nat) (old items : List Constant)
    (destination : heap[address]? = some (.set old))
    (input : heap[source]? = some (.list (items.map Mutable.Value.scalar))) :
    ReturnsValue program "merge" [.ref address, .ref source] heap (.ref address)
      (heap.set address (.set (items.foldl ScalarSet.insert old))) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.discard (Evaluates.updateSet (Evaluates.lookup rfl)
    (old.map (fun item => (.scalar item, .scalar item))) (by simp [destination, Mutable.keyEntries])
    (.cons (Evaluates.lookup rfl) .nil) (updateSet_list_scalars heap address source old items destination input)
    (by intro name same; cases same; rfl))
  exact BlockReturns.return_value (Evaluates.lookup rfl)

theorem naive.«Returns» (heap : Heap) (address source : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "set[int]")
    (sourceTyped : Mutable.Value.HasType heap (.ref source) "list[int]") :
    (SetCalls.call program "naive" [.ref address, .ref source] heap).Returns := by
  obtain ⟨old, destination, _⟩ := typed
  obtain ⟨items, input⟩ := Mutable.Value.ints_of_hasType sourceTyped
  intro choices
  exact ⟨.ref address, [], _, heap.length,
    SetCalls.finishes_of_heap (naive_result heap address source old (items.map Constant.int) destination (by simpa only [List.map_map, Function.comp_def] using input)).finishes choices 0⟩

theorem naive.«Supported» (heap : Heap) (address source : Nat) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "set[int]")
    (sourceTyped : Mutable.Value.HasType heap (.ref source) "list[int]") :
    (SetCalls.call program "naive" [.ref address, .ref source] heap).Supported := by
  intro choices
  exact (naive.«Returns» heap address source valid typed sourceTyped choices).supported

theorem merge.«Equiv(naive)» (heap : Heap) (address source : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "set[int]")
    (sourceTyped : Mutable.Value.HasType heap (.ref source) "list[int]") :
    (SetCalls.call program "merge" [.ref address, .ref source] heap).Equiv
      (SetCalls.call program "naive" [.ref address, .ref source] heap) := by
  obtain ⟨old, destination, _⟩ := typed
  obtain ⟨items, input⟩ := Mutable.Value.ints_of_hasType sourceTyped
  intro leftChoices rightChoices
  exact Mutable.Call.equiv_of_finishes
    (SetCalls.finishes_of_heap (merge_result heap address source old (items.map Constant.int) destination (by simpa only [List.map_map, Function.comp_def] using input)).finishes leftChoices 0)
    (SetCalls.finishes_of_heap (naive_result heap address source old (items.map Constant.int) destination (by simpa only [List.map_map, Function.comp_def] using input)).finishes rightChoices 0)
    (.inl rfl)

theorem merge.«Supported» :
    (∀ (heap : Heap) (address source : Nat), heap.Valid →
      Mutable.Value.HasType heap (.ref address) "set[int]" →
      Mutable.Value.HasType heap (.ref source) "list[int]" →
      (SetCalls.call program "merge" [.ref address, .ref source] heap).Supported) ∧
    (∀ (heap : Heap) (address source : Nat), heap.Valid →
      Mutable.Value.HasType heap (.ref address) "set[int]" →
      Mutable.Value.HasType heap (.ref source) "list[int]" →
      (SetCalls.call program "naive" [.ref address, .ref source] heap).Supported) := by
  constructor
  · intro heap address source _ typed sourceTyped choices
    obtain ⟨old, destination, _⟩ := typed
    obtain ⟨items, input⟩ := Mutable.Value.ints_of_hasType sourceTyped
    exact Execution.supported_of_finishes
      (SetCalls.finishes_of_heap (merge_result heap address source old (items.map Constant.int) destination (by simpa only [List.map_map, Function.comp_def] using input)).finishes choices 0)
  · exact naive.«Supported»

end tests.py.set_update
