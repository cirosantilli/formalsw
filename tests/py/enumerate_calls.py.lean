import «.formalsw».tests.py.«enumerate_calls.py.ast»
import FormalSW

namespace tests.py.enumerate_calls
open FormalSW.PyAst
private abbrev program := EnumerateCallsAst.module
private abbrev body : List Stmt := [.augAssign (.name "total") .add (.constant (.int 1))]

private theorem loop.result (heap : Mutable.Heap) (address : Nat) (items : List Mutable.Value)
    (found : heap[address]? = some (.list items)) (position : Nat) (bounded : position ≤ items.length)
    (counter total : Int) (env : HeapCalls.Env) (getTotal : env "total" = some (.scalar (.int total))) :
    ∃ finalEnv, HeapCalls.BlockContinues program env
      [.enumerateStepLoop "index" "value" (.ref address) position counter body []] heap finalEnv heap ∧
      finalEnv "total" = some (.scalar (.int (total + (items.length - position)))) := by
  have sequence : Mutable.sequence (.ref address) heap = some (.ok items, heap) := by
    simp [Mutable.sequence, found]
  by_cases active : position < items.length
  · let boundEnv := HeapCalls.setLocal (HeapCalls.setLocal env "index" (.scalar (.int counter))) "value" items[position]
    have saved : boundEnv "total" = some (.scalar (.int total)) := by
      simpa [boundEnv, HeapCalls.setLocal] using getTotal
    let nextEnv := HeapCalls.setLocal boundEnv "total" (.scalar (.int (total + 1)))
    have increment : HeapCalls.BlockContinues program boundEnv body heap nextEnv heap :=
      HeapCalls.BlockContinues.augAssign saved HeapCalls.Evaluates.constant rfl
    obtain ⟨finalEnv, rest, answer⟩ := loop.result heap address items found (position + 1) (by omega)
      (counter + 1) (total + 1) nextEnv rfl
    refine ⟨finalEnv, ?_, ?_⟩
    · apply HeapCalls.BlockContinues.enumerate_step (source := .ref address) sequence (List.getElem?_eq_getElem active)
      exact HeapCalls.BlockContinues.append increment rest
    · have adjust : total + 1 + ((items.length : Int) - (position + 1 : Nat)) =
          total + ((items.length : Int) - position) := by omega
      simpa only [adjust] using answer
  · have equal : position = items.length := by omega
    refine ⟨env, HeapCalls.BlockContinues.enumerate_done (source := .ref address) sequence ?_ HeapCalls.BlockContinues.nil, ?_⟩
    · simp [equal]
    · simpa [equal] using getTotal
termination_by items.length - position
decreasing_by omega

/-- Enumerating any shared list finishes, counts its elements, and preserves its heap. -/
theorem count.result (heap : Mutable.Heap) (address : Nat) (items : List Mutable.Value) (start : Int)
    (found : heap[address]? = some (.list items)) :
    HeapCalls.ReturnsValue program "count" [.ref address, .scalar (.int start)] heap
      (.scalar (.int items.length)) heap := by
  let initialEnv := HeapCalls.setLocal
    (HeapCalls.argumentEnv [⟨"values", some (.subscript (.name "list") (.name "int")), none⟩,
      ⟨"start", some (.name "int"), none⟩] [.ref address, .scalar (.int start)]) "total" (.scalar (.int 0))
  obtain ⟨finalEnv, loop, answer⟩ := loop.result heap address items found 0 (by omega) start 0 initialEnv rfl
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.assign (HeapCalls.Evaluates.constant (value := .int 0))
  apply HeapCalls.BlockContinues.returns
    (HeapCalls.BlockContinues.for_enumerate_start (items := items)
      (HeapCalls.Evaluates.lookup (name := "values") rfl) (HeapCalls.Evaluates.lookup (name := "start") rfl) rfl
      (by simp [Mutable.sequence, found]) loop)
  apply HeapCalls.BlockReturns.return_value
  exact HeapCalls.Evaluates.lookup (by simpa using answer)

theorem count.«Returns» (heap : Mutable.Heap) (address : Nat) (start : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "count" [.ref address, .scalar (.int start)] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (count.result heap address _ start found).returns

theorem count.«ReturnType» (heap : Mutable.Heap) (address : Nat) (start : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "count" [.ref address, .scalar (.int start)] heap).ReturnType "int" := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact .inr ⟨_, [], heap, heap.length, (count.result heap address _ start found).finishes, rfl⟩

theorem count.«Supported» (heap : Mutable.Heap) (address : Nat) (start : Int)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "count" [.ref address, .scalar (.int start)] heap).Supported :=
  (count.«Returns» heap address start valid typed).supported

end tests.py.enumerate_calls
