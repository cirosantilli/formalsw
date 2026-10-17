import «.formalsw».tests.py.«sequence_sums.py.ast»
import FormalSW

namespace tests.py.sequence_sums
open FormalSW.PyAst
private abbrev program := SequenceSumsAst.module

/-- The exact sum of arbitrary shared integer contents, with no allocation or mutation. -/
theorem direct.result (heap : Mutable.Heap) (address : Nat) (items : List Int) (start : Int)
    (found : heap[address]? = some (.list (items.map fun n => .scalar (.int n)))) :
    HeapCalls.ReturnsValue program "direct" [.ref address, .scalar (.int start)] heap
      (.scalar (.int (items.foldl Int.add start))) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.sum_integers
    (.cons (HeapCalls.Evaluates.lookup rfl) (.cons (HeapCalls.Evaluates.lookup rfl) .nil))
  simp [Mutable.sequence, found]

theorem generated.result (heap : Mutable.Heap) (address : Nat) (items : List Int) (start : Int)
    (found : heap[address]? = some (.list (items.map fun n => .scalar (.int n)))) :
    HeapCalls.ReturnsValue program "generated" [.ref address, .scalar (.int start)] heap
      (.scalar (.int (items.foldl Int.add start))) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.sum_generator_sequence
    (items := items.map fun n => .scalar (.int n)) (by intros; simp)
    (HeapCalls.Evaluates.lookup rfl)
    (by simp [Mutable.sequence, found]) (HeapCalls.Evaluates.lookup rfl) rfl
  apply HeapCalls.sum_integer_loop (values := items) items (by decide)
  · simp [HeapCalls.sequenceValue, HeapCalls.sequenceSource, Mutable.sequence, found]
  · rfl
  · simp [HeapCalls.setLocal]

theorem direct.«Returns» (heap : Mutable.Heap) (address : Nat) (start : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "direct" [.ref address, .scalar (.int start)] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (direct.result heap address items start found).returns

theorem direct.«Supported» (heap : Mutable.Heap) (address : Nat) (start : Int)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "direct" [.ref address, .scalar (.int start)] heap).Supported :=
  (direct.«Returns» heap address start valid typed).supported

theorem generated.«Returns» (heap : Mutable.Heap) (address : Nat) (start : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "generated" [.ref address, .scalar (.int start)] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (generated.result heap address items start found).returns

theorem generated.«Equiv(direct)» (heap : Mutable.Heap) (address : Nat) (start : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "generated" [.ref address, .scalar (.int start)] heap).Equiv
      (HeapCalls.call program "direct" [.ref address, .scalar (.int start)] heap) := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact Mutable.Call.equiv_of_finishes (generated.result heap address items start found).finishes
    (direct.result heap address items start found).finishes (.inl rfl)

theorem generated.«Supported» :
    (∀ (heap : Mutable.Heap) (address : Nat) (start : Int), heap.Valid →
      Mutable.Value.HasType heap (.ref address) "list[int]" →
      (HeapCalls.call program "generated" [.ref address, .scalar (.int start)] heap).Supported) ∧
    (∀ (heap : Mutable.Heap) (address : Nat) (start : Int), heap.Valid →
      Mutable.Value.HasType heap (.ref address) "list[int]" →
      (HeapCalls.call program "direct" [.ref address, .scalar (.int start)] heap).Supported) :=
  ⟨fun heap address start valid typed => (generated.«Returns» heap address start valid typed).supported,
   direct.«Supported»⟩

end tests.py.sequence_sums
