import «.cleanxy».tests.py.«parallel_shared_counter.py.ast»
import CleanXY

namespace tests.py.parallel_shared_counter
open CleanXY.PyAst

-- Explicit arguments identify the shared array and the SAME mutex for both calls.
private def calls (name : String) :=
  List.replicate 2 (parallelFunction ParallelSharedCounterAst.module name [.ref 0, .lock 0])
private def initial : SharedState := { objects := [.array [.int 0]] }

theorem increment_safe.preserves_both_updates :
    Ensures(Parallel(calls "increment_safe", initial), fun state => state.item 0 0 = some (.int 2)) := by
  native_decide

theorem increment_unsafe.can_lose_an_update :
    CanReturn(Parallel(calls "increment_unsafe", initial), { objects := [.array [.int 1]] }) := by
  native_decide

theorem increment_unsafe.two_updates_not_guaranteed :
    Not Ensures(Parallel(calls "increment_unsafe", initial), fun state => state.item 0 0 = some (.int 2)) := by
  intro guarantee
  have impossible := guarantee.of_canReturn increment_unsafe.can_lose_an_update
  contradiction

-- Both workers read zero, both yield, then both write one.
theorem increment_unsafe.losing_schedule :
    let workers := (calls "increment_unsafe").mapM id
    workers.map (fun workers => parallelReplay ⟨initial, workers⟩ [0, 1, 0, 1, 0, 1]) =
      some (.ok { objects := [.array [.int 1]] }) := by
  native_decide

end tests.py.parallel_shared_counter
