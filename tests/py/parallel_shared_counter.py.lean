import «.cleanxy».tests.py.«parallel_shared_counter.py.ast»
import CleanXY

open CleanXY.PyAst

namespace tests.py.parallel_shared_counter

theorem increment_unsafe.«Not Concurrent(run_trial)» :
    ∃  (_final : SharedState),
    ParallelRun.CanReturn (parallelRun (((List.range ((2 : Int)).toNat).map Int.ofNat).map (fun _job => parallelFunction ParallelSharedCounterAst.module "increment_unsafe" [.ref ((0)), .lock 0])) (({ objects := ([.array [.int (0)]]) } : SharedState))) _final ∧
    ((do Concurrent.check (((← Concurrent.readIntItem _final ((0)) ((0 : Int)))) == ((2 : Int))); pure ()) : Option Unit) = none
  := by
  refine ⟨{ objects := [.array [.int 1]] }, ?_, ?_⟩
  · native_decide
  · decide

theorem increment_safe.«Concurrent(run_trial)» :
    ParallelRun.Ensures (parallelRun (((List.range ((2 : Int)).toNat).map Int.ofNat).map (fun _job => parallelFunction ParallelSharedCounterAst.module "increment_safe" [.ref ((0)), .lock 0])) (({ objects := ([.array [.int (0)]]) } : SharedState))) (fun _final => ((do Concurrent.check (((← Concurrent.readIntItem _final ((0)) ((0 : Int)))) == ((2 : Int))); pure ()) : Option Unit) = some ())
  := by
  native_decide

-- The same explicit schedule is replayed against the real Python worker in
-- parallel_checks. The main obligations above come from run_trial itself.
private def calls (name : String) :=
  List.replicate 2 (parallelFunction ParallelSharedCounterAst.module name [.ref 0, .lock 0])
private def initial : SharedState := { objects := [.array [.int 0]] }

-- Both workers read zero, both yield, then both write one.
theorem increment_unsafe.losing_schedule :
    let workers := (calls "increment_unsafe").mapM id
    workers.map (fun workers => parallelReplay ⟨initial, workers⟩ [0, 1, 0, 1, 0, 1]) =
      some (.ok { objects := [.array [.int 1]] }) := by
  native_decide


end tests.py.parallel_shared_counter
