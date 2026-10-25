import «.formalsw».tests.py.«heap_memo_calls.py.ast»
import lang.py.FormalSW.HeapMemoCallRules

namespace tests.py.heap_memo_calls
open FormalSW.PyAst FormalSW.PyAst.HeapMemoCalls
private abbrev program := HeapMemoCallsAst.module

private def Pair (heap : Mutable.Heap) (value : Mutable.Value) (n : Int) : Prop :=
  ∃ address, value = .ref address ∧
    heap[address]? = some (.tuple [.scalar (.int n), .scalar (.int (n + 1))])

private def spec (heap : Mutable.Heap) (key : MemoCalls.Key) (value : Mutable.Value) : Prop :=
  ∃ n, key = ⟨"cached_pair", [n]⟩ ∧ Pair heap value n

private theorem preserves (heap extra : Mutable.Heap) : Cache.Preserves spec heap (heap ++ extra) := by
  apply Cache.preserves_append
  rintro key value ⟨n, same, address, rfl, found⟩
  refine ⟨n, same, address, rfl, ?_⟩
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

/-- Hits may return any existing address satisfying the heap-dependent invariant. -/
private theorem cached_pair.result (n : Int) (heap : Mutable.Heap) :
    ReturnsRel program spec "cached_pair" [.scalar (.int n)] heap (fun value after => Pair after value n) := by
  apply BlockReturnsRel.memoized_function (values := [n]) (by decide) rfl rfl
  · apply BlockReturnsRel.return_value
    apply (Evaluates.tuple (.cons (Evaluates.lookup rfl) (.cons
      (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl) .nil))
        (preserves heap _)).rel.consequence
    rintro value after ⟨equalValue, equalHeap⟩
    subst value
    subst after
    have pair : Pair (heap ++ [.tuple [.scalar (.int n), .scalar (.int (n + 1))]]) (.ref heap.length) n :=
      ⟨heap.length, rfl, by simp⟩
    exact ⟨pair, n, rfl, pair⟩
  · rintro value ⟨other, same, pair⟩
    have equal : n = other := by simpa [MemoCalls.Key.mk.injEq] using same
    subst other
    exact pair

/-- The actual decorated tuple-returning helper is evaluated through the cache-aware machine. -/
theorem first_component.result (n : Int) (heap : Mutable.Heap) :
    ReturnsRel program spec "first_component" [.scalar (.int n)] heap
      (fun value _ => value = .scalar (.int n)) := by
  apply BlockReturnsRel.function (by decide) rfl rfl
  apply BlockReturnsRel.return_value
  apply EvaluatesRel.subscript (b := .constant (.int 0))
    (ordinary := by intro x y z same; cases same) (basePost := fun value after => Pair after value n)
    (indexPost := fun _ middle value after => value = .scalar (.int 0) ∧ after = middle)
  · apply EvaluatesRel.call (ArgumentsRel.fixed (.cons (Evaluates.lookup rfl) .nil))
    rintro values middle ⟨equalValues, equalHeap⟩
    subst values
    subst middle
    exact cached_pair.result n heap
  · intro value middle _
    exact EvaluatesRel.constant ⟨rfl, rfl⟩
  · rintro value middle index after ⟨address, equalValue, found⟩ ⟨equalIndex, equalHeap⟩
    subst value
    subst index
    subst after
    exact ⟨.scalar (.int n), middle, by simp [Mutable.getItem, Mutable.index, found, Except.map],
      Cache.Preserves.refl, rfl⟩

theorem first_component.«Returns» (n : Int) :
    (HeapMemoCalls.scalarFunction program "first_component" [.int n]).Returns :=
  ReturnsRel.scalar_returns ((first_component.result n []).consequence (by intro value after same; exact ⟨same, True.intro⟩))

theorem first_component.«Supported» (n : Int) :
    (HeapMemoCalls.scalarFunction program "first_component" [.int n]).Supported :=
  (first_component.«Returns» n).supported

end tests.py.heap_memo_calls
