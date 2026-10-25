import «.formalsw».tests.py.«truth_captured.py.ast»
import lang.py.FormalSW.TruthCalls

namespace tests.py.truth_captured
open FormalSW.PyAst
private abbrev program := TruthCapturedAst.module

theorem within.result (heap : Mutable.Heap) (address : Nat) (items : List Int) (ceiling : Int)
    (found : heap[address]? = some (.list (items.map fun n => .scalar (.int n)))) :
    HeapCalls.ReturnsValue program "within" [.ref address, .scalar (.int ceiling)] heap
      (.scalar (.bool (items.all fun n => decide (n ≤ ceiling)))) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.all_map_with_invariant (values := items) (encode := fun n => .scalar (.int n))
    (invariant := fun env => env "ceiling" = some (.scalar (.int ceiling)))
    (by intros; simp) (by intros; simp) (by intros; simp) (HeapCalls.Evaluates.lookup rfl)
  · simp [Mutable.sequence, found]
  · intro env n current
    simpa [HeapCalls.setLocal] using current
  · simp [HeapCalls.comprehensionTargetsEnv, targetLocals]
    rfl
  · intro env n current getValue
    exact HeapCalls.Evaluates.compare (HeapCalls.Evaluates.lookup getValue) (HeapCalls.Evaluates.lookup current)
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])

theorem within.«Returns» (heap : Mutable.Heap) (address : Nat) (ceiling : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "within" [.ref address, .scalar (.int ceiling)] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (within.result heap address items ceiling found).returns

theorem within.«Supported» (heap : Mutable.Heap) (address : Nat) (ceiling : Int)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "within" [.ref address, .scalar (.int ceiling)] heap).Supported :=
  (within.«Returns» heap address ceiling valid typed).supported

end tests.py.truth_captured
