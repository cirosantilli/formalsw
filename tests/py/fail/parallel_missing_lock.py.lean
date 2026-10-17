import «.formalsw».tests.py.fail.«parallel_missing_lock.py.ast»
import FormalSW
namespace tests.py.fail.parallel_missing_lock
open FormalSW.PyAst

theorem increment.preserves_both_updates :
    Ensures(Parallel(List.replicate 2
      (parallelFunction ParallelMissingLockAst.module "increment" [.ref 0, .lock 0]),
      { objects := [.array [.int 0]] }), fun state => state.item 0 0 = some (.int 2)) := by
  native_decide
end tests.py.fail.parallel_missing_lock
