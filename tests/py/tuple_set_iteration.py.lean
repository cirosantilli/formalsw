import «.formalsw».tests.py.«tuple_set_iteration.py.ast»
import FormalSW

namespace tests.py.tuple_set_iteration
open FormalSW.PyAst
private abbrev program := TupleSetIterationAst.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
private abbrev body : List Stmt := [.augAssign (.name "total") .add (.constant (.int 1))]

private theorem count_loop (choices : ChoiceSchedule) (heap : Mutable.Heap) (address : Nat)
    (original : List (HashKey × Mutable.Value)) (remaining : List SequenceSource) (found : heap[address]? = some (.keySet original))
    (total : Int) (env : HeapCalls.Env) (accumulator : env "total" = some (number total))
    (anchors : Nat) (stack : List HeapCalls.Frame) (used : Nat) :
    ∃ finalUsed, SetCalls.Reaches choices program anchors
      ⟨⟨.block [.keySetStepLoop "value" address original.length remaining body [], .return (.name "total")] env,
        stack, heap⟩, used⟩
      ⟨⟨.value (number (total + remaining.length)), stack, heap⟩, finalUsed⟩ := by
  cases remaining with
  | nil =>
      refine ⟨used, .next (following := ⟨⟨.block [.return (.name "total")] env, stack, heap⟩, used⟩) ?_ ?_⟩
      · simp [SetCalls.step, HeapCalls.step, SetCalls.iteratorStep, Mutable.keyEntries, found]
      · simpa using SetCalls.Reaches.of_heap
          ((HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup accumulator)) anchors stack) choices used
  | cons head tail =>
      let index := choices used % (head :: tail).length
      have bound : index < (head :: tail).length := Nat.mod_lt _ (by simp)
      let item := (head :: tail)[index]
      have selected : (head :: tail)[index]? = some item := List.getElem?_eq_getElem bound
      have selected' : (head :: tail)[choices used % (tail.length + 1)]? = some item := selected
      let rest := (head :: tail).eraseIdx index
      let boundEnv := HeapCalls.setLocal env "value" (HeapCalls.sequenceValue item)
      let updatedEnv := HeapCalls.setLocal boundEnv "total" (number (total + 1))
      have emitted : HeapCalls.BlockContinues program boundEnv body heap updatedEnv heap := by
        apply HeapCalls.BlockContinues.augAssign
          (left := number total) (right := number 1) (middle := heap)
        · simpa [boundEnv, HeapCalls.setLocal] using accumulator
        · exact HeapCalls.Evaluates.constant
        · rfl
      obtain ⟨finalUsed, completed⟩ := count_loop choices heap address original rest found (total + 1)
        updatedEnv (by simp [updatedEnv, HeapCalls.setLocal]) anchors stack (used + 1)
      refine ⟨finalUsed, .next (following := ⟨⟨.block (body ++ [.keySetStepLoop "value" address original.length rest body [],
        .return (.name "total")]) boundEnv, stack, heap⟩, used + 1⟩) ?_ ?_⟩
      · simp [SetCalls.step, HeapCalls.step, SetCalls.iteratorStep, Mutable.keyEntries, found, selected', index,
          body, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, rest, boundEnv]
      · have path := SetCalls.Reaches.of_heap
          (emitted [.keySetStepLoop "value" address original.length rest body [], .return (.name "total")] anchors stack)
          choices (used + 1)
        have same : total + 1 + rest.length = total + (head :: tail).length := by
          have length := List.length_eraseIdx_of_lt bound
          simp only [rest] at *
          omega
        rw [same] at completed
        exact path.trans completed
termination_by remaining.length
decreasing_by
  change ((head :: tail).eraseIdx index).length < (head :: tail).length
  rw [List.length_eraseIdx_of_lt bound]
  simp

theorem count_result (choices : ChoiceSchedule) (heap : Mutable.Heap) (address : Nat)
    (items : List (HashKey × Mutable.Value)) (found : heap[address]? = some (.keySet items)) :
    ((SetCalls.call program "count" [.ref address] heap).run choices).Finishes
      ⟨.ok (number items.length), [], heap, heap.length⟩ := by
  let env := HeapCalls.setLocal
    (HeapCalls.argumentEnv [⟨"values", some (.subscript (.name "set") (.subscript (.name "tuple") (.tuple [.name "int", .name "int"]))), none⟩] [.ref address])
    "total" (number 0)
  have entry : SetCalls.Reaches choices program heap.length
      ⟨⟨.operation (.call "count") [.ref address], [], heap⟩, 0⟩
      ⟨⟨.block [.keySetStepLoop "value" address items.length (items.map (fun item => HeapCalls.sequenceSource item.2)) body [], .return (.name "total")] env,
        [], heap⟩, 0⟩ := by
    apply SetCalls.Reaches.next rfl
    apply SetCalls.Reaches.next rfl
    apply SetCalls.Reaches.next rfl
    apply SetCalls.Reaches.next rfl
    apply SetCalls.Reaches.next rfl
    apply SetCalls.Reaches.next rfl
    exact .next (by simp [SetCalls.step, HeapCalls.step, HeapCalls.run, Mutable.sequence,
      found, SetCalls.iteratorStep, Mutable.unsupported, env, body, HeapCalls.functionEnv]) .refl
  obtain ⟨finalUsed, loop⟩ := count_loop choices heap address items (items.map (fun item => HeapCalls.sequenceSource item.2)) found 0 env
    (by simp [env, HeapCalls.setLocal]) heap.length [] 0
  have finished := (entry.trans loop).finishes (.done rfl)
  simpa using finished

private theorem fast_count.result (heap : Mutable.Heap) (address : Nat) (items : List (HashKey × Mutable.Value))
    (found : heap[address]? = some (.keySet items)) :
    HeapCalls.ReturnsValue program "fast_count" [.ref address] heap (number items.length) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  exact HeapCalls.Evaluates.builtin (.cons (.lookup rfl) .nil)
    (by simp [HeapCalls.primitive, Mutable.length, found])

theorem counts_equivalent (heap : Mutable.Heap) (address : Nat)
    (items : List (HashKey × Mutable.Value)) (found : heap[address]? = some (.keySet items)) :
    (SetCalls.call program "fast_count" [.ref address] heap).Equiv
      (SetCalls.call program "count" [.ref address] heap) := by
  intro leftChoices rightChoices
  apply Mutable.Call.equiv_of_finishes
    (a := (SetCalls.call program "fast_count" [.ref address] heap).run leftChoices)
    (b := (SetCalls.call program "count" [.ref address] heap).run rightChoices)
    (SetCalls.finishes_of_heap (fast_count.result heap address items found).finishes leftChoices 0)
    (count_result rightChoices heap address items found)
  exact .inl rfl

private theorem tuple_set_storage (heap : Mutable.Heap) (address : Nat)
    (typed : Mutable.Value.HasContainerType heap (.ref address) (.set (.tuple [.scalar "int", .scalar "int"]))) :
    heap[address]? = some (.set []) ∨ ∃ items, heap[address]? = some (.keySet items) := by
  cases typed with
  | scalarSet found elements =>
    left
    rename_i items
    cases items with
    | nil => exact found
    | cons first rest =>
      have impossible := elements first (List.mem_cons_self ..)
      cases impossible
  | keyedSet found _ => exact .inr ⟨_, found⟩

private theorem count_empty (choices : ChoiceSchedule) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.set [])) :
    ((SetCalls.call program "count" [.ref address] heap).run choices).Finishes
      ⟨.ok (number 0), [], heap, heap.length⟩ := by
  let env := HeapCalls.setLocal
    (HeapCalls.argumentEnv [⟨"values", some (.subscript (.name "set")
      (.subscript (.name "tuple") (.tuple [.name "int", .name "int"]))), none⟩] [.ref address]) "total" (number 0)
  have entry : SetCalls.Reaches choices program heap.length
      ⟨⟨.operation (.call "count") [.ref address], [], heap⟩, 0⟩
      ⟨⟨.block [.return (.name "total")] env, [], heap⟩, 0⟩ := by
    apply SetCalls.Reaches.next rfl
    apply SetCalls.Reaches.next rfl
    apply SetCalls.Reaches.next rfl
    apply SetCalls.Reaches.next rfl
    apply SetCalls.Reaches.next rfl
    apply SetCalls.Reaches.next rfl
    apply SetCalls.Reaches.next (following := ⟨⟨.block
      [.setStepLoop "value" address [] [] body [], .return (.name "total")] env, [], heap⟩, 0⟩)
    · simp [SetCalls.step, HeapCalls.step, HeapCalls.run, Mutable.sequence, found,
        SetCalls.iteratorStep, Mutable.unsupported, env, body, HeapCalls.functionEnv]
    · exact .next (by simp [SetCalls.step, HeapCalls.step, SetCalls.iteratorStep, found]) .refl
  have returned : HeapCalls.BlockReturns program env [.return (.name "total")] heap (number 0) heap :=
    .return_value (.lookup (by simp [env, HeapCalls.setLocal]))
  exact (entry.trans (SetCalls.Reaches.of_heap (returned heap.length []) choices 0)).finishes (.done rfl)

theorem count.«Supported» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasContainerType heap (.ref address) (.set (.tuple [.scalar "int", .scalar "int"]))) :
    (SetCalls.call program "count" [.ref address] heap).Supported := by
  intro choices
  rcases tuple_set_storage heap address typed with found | ⟨items, found⟩
  · exact Execution.supported_of_finishes (count_empty choices heap address found)
  · exact Execution.supported_of_finishes (count_result choices heap address items found)

theorem fast_count.«Supported» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasContainerType heap (.ref address) (.set (.tuple [.scalar "int", .scalar "int"]))) :
    (HeapCalls.call program "fast_count" [.ref address] heap).Supported := by
  rcases tuple_set_storage heap address typed with found | ⟨items, found⟩
  · have returned : HeapCalls.ReturnsValue program "fast_count" [.ref address] heap (number 0) heap := by
      apply HeapCalls.BlockReturns.function rfl rfl
      apply HeapCalls.BlockReturns.return_value
      exact HeapCalls.Evaluates.builtin (.cons (.lookup rfl) .nil)
        (by simp [HeapCalls.primitive, Mutable.length, found])
    exact Execution.supported_of_finishes returned.finishes
  · exact Execution.supported_of_finishes (fast_count.result heap address items found).finishes

end tests.py.tuple_set_iteration
