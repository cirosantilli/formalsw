import «.formalsw».tests.py.«set_iteration.py.ast»
import FormalSW

namespace tests.py.set_iteration
open FormalSW.PyAst
private abbrev program := SetIterationAst.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
private abbrev body : List Stmt := [.augAssign (.name "total") .add (.constant (.int 1))]

private theorem count_loop (choices : ChoiceSchedule) (heap : Mutable.Heap) (address : Nat)
    (original remaining : List Constant) (found : heap[address]? = some (.set original))
    (total : Int) (env : HeapCalls.Env) (accumulator : env "total" = some (number total))
    (anchors : Nat) (stack : List HeapCalls.Frame) (used : Nat) :
    ∃ finalUsed, SetCalls.Reaches choices program anchors
      ⟨⟨.block [.setStepLoop "value" address original remaining body [], .return (.name "total")] env,
        stack, heap⟩, used⟩
      ⟨⟨.value (number (total + remaining.length)), stack, heap⟩, finalUsed⟩ := by
  cases remaining with
  | nil =>
      refine ⟨used, .next (following := ⟨⟨.block [.return (.name "total")] env, stack, heap⟩, used⟩) ?_ ?_⟩
      · simp [SetCalls.step, HeapCalls.step, SetCalls.iteratorStep, found]
      · simpa using SetCalls.Reaches.of_heap
          ((HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup accumulator)) anchors stack) choices used
  | cons head tail =>
      let index := choices used % (head :: tail).length
      have bound : index < (head :: tail).length := Nat.mod_lt _ (by simp)
      let item := (head :: tail)[index]
      have selected : (head :: tail)[index]? = some item := List.getElem?_eq_getElem bound
      have selected' : (head :: tail)[choices used % (tail.length + 1)]? = some item := selected
      let rest := (head :: tail).eraseIdx index
      let boundEnv := HeapCalls.setLocal env "value" (.scalar item)
      let updatedEnv := HeapCalls.setLocal boundEnv "total" (number (total + 1))
      have emitted : HeapCalls.BlockContinues program boundEnv body heap updatedEnv heap := by
        apply HeapCalls.BlockContinues.augAssign
          (left := number total) (right := number 1) (middle := heap)
        · simpa [boundEnv, HeapCalls.setLocal] using accumulator
        · exact HeapCalls.Evaluates.constant
        · rfl
      obtain ⟨finalUsed, completed⟩ := count_loop choices heap address original rest found (total + 1)
        updatedEnv (by simp [updatedEnv, HeapCalls.setLocal]) anchors stack (used + 1)
      refine ⟨finalUsed, .next (following := ⟨⟨.block (body ++ [.setStepLoop "value" address original rest body [],
        .return (.name "total")]) boundEnv, stack, heap⟩, used + 1⟩) ?_ ?_⟩
      · simp [SetCalls.step, HeapCalls.step, SetCalls.iteratorStep, found, selected', index,
          body, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, rest, boundEnv]
      · have path := SetCalls.Reaches.of_heap
          (emitted [.setStepLoop "value" address original rest body [], .return (.name "total")] anchors stack)
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

theorem count.result (choices : ChoiceSchedule) (heap : Mutable.Heap) (address : Nat)
    (items : List Constant) (found : heap[address]? = some (.set items)) :
    ((SetCalls.call program "count" [.ref address] heap).run choices).Finishes
      ⟨.ok (number items.length), [], heap, heap.length⟩ := by
  let env := HeapCalls.setLocal
    (HeapCalls.argumentEnv [⟨"values", some (.subscript (.name "set") (.name "int")), none⟩] [.ref address])
    "total" (number 0)
  have entry : SetCalls.Reaches choices program heap.length
      ⟨⟨.operation (.call "count") [.ref address], [], heap⟩, 0⟩
      ⟨⟨.block [.setStepLoop "value" address items items body [], .return (.name "total")] env,
        [], heap⟩, 0⟩ := by
    apply SetCalls.Reaches.next rfl
    apply SetCalls.Reaches.next rfl
    apply SetCalls.Reaches.next rfl
    apply SetCalls.Reaches.next rfl
    apply SetCalls.Reaches.next rfl
    apply SetCalls.Reaches.next rfl
    exact .next (by simp [SetCalls.step, HeapCalls.step, HeapCalls.run, Mutable.sequence,
      found, SetCalls.iteratorStep, Mutable.unsupported, env, body, HeapCalls.functionEnv]) .refl
  obtain ⟨finalUsed, loop⟩ := count_loop choices heap address items items found 0 env
    (by simp [env, HeapCalls.setLocal]) heap.length [] 0
  have finished := (entry.trans loop).finishes (.done rfl)
  simpa using finished

theorem count.«Returns» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "set[int]") :
    (SetCalls.call program "count" [.ref address] heap).Returns := by
  obtain ⟨items, found, _⟩ := typed
  intro choices
  exact ⟨number items.length, [], heap, heap.length, count.result choices heap address items found⟩

theorem count.«Supported» (heap : Mutable.Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "set[int]") :
    (SetCalls.call program "count" [.ref address] heap).Supported := by
  intro choices
  exact (count.«Returns» heap address valid typed choices).supported

private theorem fast_count.result (heap : Mutable.Heap) (address : Nat) (items : List Constant)
    (found : heap[address]? = some (.set items)) :
    HeapCalls.ReturnsValue program "fast_count" [.ref address] heap (number items.length) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  exact HeapCalls.Evaluates.builtin (.cons (.lookup rfl) .nil)
    (by simp [HeapCalls.primitive, Mutable.length, found])

theorem fast_count.«Equiv(count)» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "set[int]") :
    (SetCalls.call program "fast_count" [.ref address] heap).Equiv
      (SetCalls.call program "count" [.ref address] heap) := by
  obtain ⟨items, found, _⟩ := typed
  intro leftChoices rightChoices
  apply Mutable.Call.equiv_of_finishes
    (a := (SetCalls.call program "fast_count" [.ref address] heap).run leftChoices)
    (b := (SetCalls.call program "count" [.ref address] heap).run rightChoices)
    (SetCalls.finishes_of_heap (fast_count.result heap address items found).finishes leftChoices 0)
    (count.result rightChoices heap address items found)
  exact .inl rfl

theorem fast_count.«Supported» :
    (∀ (heap : Mutable.Heap) (address : Nat), heap.Valid →
      Mutable.Value.HasType heap (.ref address) "set[int]" →
      (SetCalls.call program "fast_count" [.ref address] heap).Supported) ∧
    (∀ (heap : Mutable.Heap) (address : Nat), heap.Valid →
      Mutable.Value.HasType heap (.ref address) "set[int]" →
      (SetCalls.call program "count" [.ref address] heap).Supported) := by
  constructor
  · intro heap address _ typed
    obtain ⟨items, found, _⟩ := typed
    intro choices
    exact Execution.supported_of_finishes
      (SetCalls.finishes_of_heap (fast_count.result heap address items found).finishes choices 0)
  · exact count.«Supported»

end tests.py.set_iteration
