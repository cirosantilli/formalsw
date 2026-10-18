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

theorem roundtripped.result (heap : Mutable.Heap) (address : Nat) (items : List Int) (start : Int)
    (found : heap[address]? = some (.list (items.map fun n => .scalar (.int n)))) :
    HeapCalls.ReturnsValue program "roundtripped" [.ref address, .scalar (.int start)] heap
      (.scalar (.int (items.foldl Int.add start))) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.sum_generator_sequence
    (items := items.map fun n => .scalar (.int n)) (by intros; simp)
    (HeapCalls.Evaluates.lookup rfl)
    (by simp [Mutable.sequence, found]) (HeapCalls.Evaluates.lookup rfl) rfl
  apply HeapCalls.sum_map_loop (values := items) (encode := fun n => .scalar (.int n))
    (number := id) items (by decide)
  · simp [HeapCalls.sequenceValue, HeapCalls.sequenceSource, Mutable.sequence, found]
  · intro env item lookup
    apply HeapCalls.Evaluates.builtin (values := [.scalar (.string (toString item))])
      (.cons (HeapCalls.Evaluates.builtin (.cons (HeapCalls.Evaluates.lookup lookup) .nil) rfl) .nil)
    simp only [HeapCalls.primitive, List.mapM_cons, List.mapM_nil]
    change HeapCalls.scalarResult (Calls.integerConversion [.string (toString item)]) heap = _
    rw [Calls.integerConversion_int]
    rfl
  · rfl
  · simp [HeapCalls.setLocal]

theorem roundtripped.«Returns» (heap : Mutable.Heap) (address : Nat) (start : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "roundtripped" [.ref address, .scalar (.int start)] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (roundtripped.result heap address items start found).returns

theorem roundtripped.«Equiv(direct)» (heap : Mutable.Heap) (address : Nat) (start : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "roundtripped" [.ref address, .scalar (.int start)] heap).Equiv
      (HeapCalls.call program "direct" [.ref address, .scalar (.int start)] heap) := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact Mutable.Call.equiv_of_finishes (roundtripped.result heap address items start found).finishes
    (direct.result heap address items start found).finishes (.inl rfl)

theorem roundtripped.«Supported» :
    (∀ (heap : Mutable.Heap) (address : Nat) (start : Int), heap.Valid →
      Mutable.Value.HasType heap (.ref address) "list[int]" →
      (HeapCalls.call program "roundtripped" [.ref address, .scalar (.int start)] heap).Supported) ∧
    (∀ (heap : Mutable.Heap) (address : Nat) (start : Int), heap.Valid →
      Mutable.Value.HasType heap (.ref address) "list[int]" →
      (HeapCalls.call program "direct" [.ref address, .scalar (.int start)] heap).Supported) :=
  ⟨fun heap address start valid typed => (roundtripped.«Returns» heap address start valid typed).supported,
   direct.«Supported»⟩

end tests.py.sequence_sums
