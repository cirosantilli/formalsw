import «.formalsw».tests.py.«sets.py.ast»
import FormalSW

open FormalSW.PyAst

namespace tests.py.sets

private abbrev program := SetsAst.module

private theorem singleton.result (n : Int) :
    HeapCalls.ReturnsValue program "singleton" [.scalar (.int n)] [] (.ref 0) [.set [.int n]] := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.assign (value := .ref 0) (middle := [.set []])
  · exact HeapCalls.Evaluates.builtin .nil rfl
  · apply HeapCalls.BlockReturns.discard
    · simpa [ScalarSet.insert, ScalarSet.contains] using
        (HeapCalls.Evaluates.add (module := program) (HeapCalls.Evaluates.lookup rfl)
          (show ([Mutable.Object.set []] : Mutable.Heap)[0]? = some (.set []) from rfl)
          (HeapCalls.Evaluates.lookup (name := "n") rfl) rfl)
    · exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup rfl)

theorem singleton.«Returns» (n : Int) :
    (HeapCalls.call program "singleton" [.scalar (.int n)] []).Returns :=
  (singleton.result n).returns

theorem singleton.«ReturnType» (n : Int) :
    (HeapCalls.call program "singleton" [.scalar (.int n)] []).ReturnType "set[int]" := by
  refine .inr ⟨.ref 0, [], [.set [.int n]], 0, (singleton.result n).finishes, ?_⟩
  simp [Mutable.Value.HasType, Data.typeName]

theorem singleton.«Supported» (n : Int) :
    (HeapCalls.call program "singleton" [.scalar (.int n)] []).Supported :=
  (singleton.«Returns» n).supported

private theorem insert.result (heap : Mutable.Heap) (address : Nat) (n : Int)
    (items : List Constant) (found : heap[address]? = some (.set items)) :
    HeapCalls.ReturnsValue program "insert" [.ref address, .scalar (.int n)] heap (.scalar .none)
      (heap.set address (.set (ScalarSet.insert items (.int n)))) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.discard
  · exact HeapCalls.Evaluates.add (HeapCalls.Evaluates.lookup rfl) found
      (HeapCalls.Evaluates.lookup rfl) found
  · intro anchors stack
    exact .next rfl .refl

theorem insert.«Returns» (heap : Mutable.Heap) (address : Nat) (n : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "set[int]") :
    (HeapCalls.call program "insert" [.ref address, .scalar (.int n)] heap).Returns := by
  obtain ⟨items, found, _⟩ := typed
  exact (insert.result heap address n items found).returns

theorem insert.«Supported» (heap : Mutable.Heap) (address : Nat) (n : Int)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "set[int]") :
    (HeapCalls.call program "insert" [.ref address, .scalar (.int n)] heap).Supported :=
  (insert.«Returns» heap address n valid typed).supported

private theorem duplicate.result (heap : Mutable.Heap) (address : Nat) (n : Int)
    (items : List Constant) (found : heap[address]? = some (.set items)) :
    HeapCalls.ReturnsValue program "duplicate" [.ref address, .scalar (.int n)] heap (.scalar .none)
      (heap.set address (.set (ScalarSet.insert items (.int n)))) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.discard
  · exact HeapCalls.Evaluates.add (HeapCalls.Evaluates.lookup rfl) found
      (HeapCalls.Evaluates.lookup rfl) found
  · have updated : (heap.set address (.set (ScalarSet.insert items (.int n))))[address]? =
        some (.set (ScalarSet.insert items (.int n))) := by
      simp [List.getElem?_set_self', found]
    apply HeapCalls.BlockReturns.discard
      (middle := heap.set address (.set (ScalarSet.insert items (.int n))))
    · simpa [ScalarSet.insert_idempotent] using
        (HeapCalls.Evaluates.add (module := program)
          (env := HeapCalls.argumentEnv [{name := "values", annotation := none}, {name := "n", annotation := none}]
            [.ref address, .scalar (.int n)]) (value := .int n)
          (HeapCalls.Evaluates.lookup (name := "values") rfl) updated
          (HeapCalls.Evaluates.lookup (name := "n") rfl) updated)
    · intro anchors stack
      exact .next rfl .refl

theorem duplicate.«Equiv(insert)» (heap : Mutable.Heap) (address : Nat) (n : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "set[int]") :
    (HeapCalls.call program "duplicate" [.ref address, .scalar (.int n)] heap).Equiv
      (HeapCalls.call program "insert" [.ref address, .scalar (.int n)] heap) := by
  obtain ⟨items, found, _⟩ := typed
  exact Mutable.Call.equiv_of_finishes (duplicate.result heap address n items found).finishes
    (insert.result heap address n items found).finishes (.inl rfl)

theorem duplicate.«Supported» :
    (∀ (heap : Mutable.Heap) (address : Nat) (n : Int), heap.Valid →
      Mutable.Value.HasType heap (.ref address) "set[int]" →
      (HeapCalls.call program "duplicate" [.ref address, .scalar (.int n)] heap).Supported) ∧
    (∀ (heap : Mutable.Heap) (address : Nat) (n : Int), heap.Valid →
      Mutable.Value.HasType heap (.ref address) "set[int]" →
      (HeapCalls.call program "insert" [.ref address, .scalar (.int n)] heap).Supported) := by
  constructor
  · intro heap address n _ typed
    obtain ⟨items, found, _⟩ := typed
    exact (duplicate.result heap address n items found).returns.supported
  · exact insert.«Supported»

end tests.py.sets
