import «.formalsw».tests.py.«slice_interval.py.ast»
import lang.py.FormalSW.HeapCalls

namespace tests.py.slice_interval
open FormalSW.PyAst HeapCalls

theorem window_result (values : List Int) (start stop : Nat) (heap : Mutable.Heap) (address : Nat)
    (ordered : start ≤ stop) (bound : stop ≤ values.length)
    (found : heap[address]? = some (.list (values.map (fun value => .scalar (.int value))))) :
    ReturnsValue SliceIntervalAst.module "window" [.ref address, .scalar (.int start), .scalar (.int stop)]
      heap (.ref heap.length)
      (heap ++ [.list (((values.drop start).take (stop - start)).map (fun value => .scalar (.int value)))]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.slice
    (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl)
      (.cons (Evaluates.lookup rfl) (.cons Evaluates.constant .nil))))
  simpa only [List.map_drop, List.map_take] using
    Mutable.getSlice_list_interval heap address (values.map (fun value => .scalar (.int value)))
      start stop ordered (by simpa using bound) found

end tests.py.slice_interval
