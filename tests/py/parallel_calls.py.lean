import «.formalsw».tests.py.«parallel_calls.py.ast»
import FormalSW
namespace tests.py.parallel_calls
open FormalSW.PyAst

theorem module_worker_calls :
    CanReturn(Parallel([parallelFunction ParallelCallsAst.module "write_last" [.ref 0, .int 9]],
      { objects := [.array [.int 3, .int 4]] }), { objects := [.array [.int 3, .int 9]] }) := by native_decide

theorem write_slot.writes_the_requested_slot :
    CanReturn(Parallel([parallelFunction ParallelCallsAst.module "write_slot" [.int 1, .ref 0, .int 7]],
      { objects := [.array [.int 0, .int 0]] }), { objects := [.array [.int 0, .int 7]] }) := by native_decide

theorem write_other.independent_writes :
    Ensures(Parallel([
      parallelFunction ParallelCallsAst.module "write_slot" [.int 1, .ref 0, .int 7],
      parallelFunction ParallelCallsAst.module "write_other" [.ref 0]],
      { objects := [.array [.int 0, .int 0]] }),
      fun state => state.item 0 0 = some (.int 5) ∧ state.item 0 1 = some (.int 7)) := by native_decide

theorem add_amount.updates_scalar_field :
    CanReturn(Parallel([parallelFunction ParallelCallsAst.module "add_amount" [.ref 0, .int 3]],
      { objects := [.object [("value", .int 4)]] }),
      { objects := [.object [("value", .int 7)]] }) := by native_decide
end tests.py.parallel_calls
