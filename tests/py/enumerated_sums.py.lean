import «.formalsw».tests.py.«enumerated_sums.py.ast»
import FormalSW

namespace tests.py.enumerated_sums
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := EnumeratedSumsAst.module

/-- An arbitrary signed index and shared integer list produce the exact weighted sum. -/
theorem weighted.result (heap : Mutable.Heap) (address : Nat) (values : List Int) (start : Int)
    (found : heap[address]? = some (.list (values.map (fun n => .scalar (.int n))))) :
    ReturnsValue program "weighted" [.ref address, .scalar (.int start)] heap
      (.scalar (.int (indexedSum (fun i n => i * n) start 0 values))) heap := by
  have sequence : Mutable.sequence (.ref address) heap =
      some (.ok (values.map (fun n => .scalar (.int n))), heap) := by
    simp [Mutable.sequence, found]
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_generator_targets_enumerate
    (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)) rfl sequence rfl Evaluates.constant rfl
  apply sum_enumerate_loop (source := .ref address) (heap := heap) (values := values)
    (encode := fun n => .scalar (.int n)) values (by decide) (by decide) (by decide) sequence
  · intro env counter value indexLookup valueLookup
    exact Evaluates.binary (Evaluates.lookup indexLookup) (Evaluates.lookup valueLookup) rfl
  · rfl
  · simp [setLocal]

theorem weighted.«Returns» (heap : Mutable.Heap) (address : Nat) (start : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "weighted" [.ref address, .scalar (.int start)] heap).Returns := by
  obtain ⟨values, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (weighted.result heap address values start found).returns

theorem weighted.«Supported» (heap : Mutable.Heap) (address : Nat) (start : Int)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "weighted" [.ref address, .scalar (.int start)] heap).Supported :=
  (weighted.«Returns» heap address start valid typed).supported

end tests.py.enumerated_sums
