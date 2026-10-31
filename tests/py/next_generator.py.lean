import «.formalsw».tests.py.«next_generator.py.ast»
import FormalSW

namespace tests.py.next_generator
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := NextGeneratorAst.module
private def encode (n : Int) : Mutable.Value := .scalar (.int n)
private def accepted (threshold value : Int) : Bool := decide (threshold ≤ value)
private def answer (values : List Int) (threshold : Int) : Mutable.Value :=
  ((values.find? (accepted threshold)).map encode).getD (encode threshold)
private def condition : Expr := .compare (.name "value") [(.gtE, .name "threshold")]

private theorem scan (heap : Heap) (address : Nat) (values : List Int) (threshold : Int)
    (found : heap[address]? = some (.list (values.map encode))) (env : Mutable.Env)
    (fallback : String) (different : fallback ≠ "value")
    (getThreshold : env "threshold" = some (encode threshold))
    (getFallback : env fallback = some (encode threshold)) :
    BlockReturns program env
      [.sequenceStepLoop "value" (.ref address) 0
        [.ifThen condition [.return (.name "value")] []] [], .return (.name fallback)]
      heap (answer values threshold) heap := by
  let invariant := fun inner : Mutable.Env =>
    inner "threshold" = some (encode threshold) ∧ inner fallback = some (encode threshold)
  apply find_sequence_loop values encode (accepted threshold) condition (.name "value")
    (.name fallback) "value" (.ref address) heap (encode threshold) invariant
  · intro inner item valid
    simpa [invariant, setLocal, different] using valid
  · intro inner item valid lookup
    exact Evaluates.compare (Evaluates.lookup lookup) (Evaluates.lookup valid.1) rfl
  · intro inner item _ lookup
    exact Evaluates.lookup lookup
  · intro inner valid
    exact Evaluates.lookup valid.2
  · simp [sequenceValue, Mutable.sequence, found]
  · exact ⟨getThreshold, getFallback⟩
  · rfl

theorem reference.result (heap : Heap) (address : Nat) (values : List Int) (threshold : Int)
    (found : heap[address]? = some (.list (values.map encode))) :
    ReturnsValue program "reference" [.ref address, encode threshold] heap
      (answer values threshold) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.for_sequence (items := values.map encode)
    (by intro arguments impossible; cases impossible)
    (Evaluates.lookup rfl) (by simp [Mutable.sequence, found])
  exact scan heap address values threshold found _ "threshold" (by decide) rfl rfl

theorem solve.result (heap : Heap) (address : Nat) (values : List Int) (threshold : Int)
    (found : heap[address]? = some (.list (values.map encode))) :
    ReturnsValue program "solve" [.ref address, encode threshold] heap
      (answer values threshold) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.next_generator_sequence (fallback := some (.name "threshold"))
    (by intro arguments impossible; cases impossible)
    (by intro arguments impossible; cases impossible)
    (by intro arguments impossible; cases impossible) (Evaluates.lookup rfl)
    (nextSequence_list heap address _ found) (Evaluates.lookup rfl)
  apply scan heap address values threshold found _ nextDefault (by decide)
  · simp [nextEnv, setLocal, nextDefault, comprehensionTargetsEnv, targetLocals,
      HeapCalls.functionEnv, HeapCalls.argumentEnv, List.lookup]
  · simp [nextEnv, setLocal]

theorem reference.«Returns» (heap : Heap) (address : Nat) (threshold : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "reference" [.ref address, encode threshold] heap).Returns := by
  obtain ⟨values, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (reference.result heap address values threshold found).returns

theorem reference.«Supported» (heap : Heap) (address : Nat) (threshold : Int)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "reference" [.ref address, encode threshold] heap).Supported :=
  (reference.«Returns» heap address threshold valid typed).supported

theorem solve.«Returns» (heap : Heap) (address : Nat) (threshold : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "solve" [.ref address, encode threshold] heap).Returns := by
  obtain ⟨values, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (solve.result heap address values threshold found).returns

theorem solve.«Equiv(reference)» (heap : Heap) (address : Nat) (threshold : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "solve" [.ref address, encode threshold] heap).Equiv
      (HeapCalls.call program "reference" [.ref address, encode threshold] heap) := by
  obtain ⟨values, found⟩ := Mutable.Value.ints_of_hasType typed
  exact Mutable.Call.equiv_of_finishes (solve.result heap address values threshold found).finishes
    (reference.result heap address values threshold found).finishes (.inl rfl)

theorem solve.«Supported» :
    (∀ heap address threshold, heap.Valid →
      Mutable.Value.HasType heap (.ref address) "list[int]" →
      (HeapCalls.call program "solve" [.ref address, encode threshold] heap).Supported) ∧
    (∀ heap address threshold, heap.Valid →
      Mutable.Value.HasType heap (.ref address) "list[int]" →
      (HeapCalls.call program "reference" [.ref address, encode threshold] heap).Supported) := by
  constructor
  · intro heap address threshold valid typed
    exact (solve.«Returns» heap address threshold valid typed).supported
  · exact reference.«Supported»

end tests.py.next_generator
