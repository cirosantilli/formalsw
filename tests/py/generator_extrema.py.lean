import «.formalsw».tests.py.«generator_extrema.py.ast»
import lang.py.FormalSW.HeapCalls

namespace tests.py.generator_extrema
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := GeneratorExtremaAst.module

/-- A fallback never competes with a yielded item, even for negative inputs. -/
private theorem singleton_eval (env : HeapCalls.Env) (heap : Heap) (n : Int)
    (found : env "n" = some (.scalar (.int n))) :
    Evaluates program env
      (.consumeGenerator (extremumConsumer true (some (.constant (.int 0)))) (.name "n")
        [(.name "_", .call (.name "range") [.constant (.int 1)], [])])
      heap (.scalar (.int n)) heap := by
  apply Evaluates.extremum_generator_range (.cons Evaluates.constant .nil) rfl Evaluates.constant
  apply BlockReturns.range_step rfl
  have valueFound :
      (setLocal (extremumEnv (comprehensionTargetsEnv env
        [(.name "_", .call (.name "range") [.constant (.int 1)], [])]) (.scalar (.int 0)))
        "_" (.scalar (.int 0))) "n" = some (.scalar (.int n)) := by
    simpa [setLocal, extremumEnv, comprehensionTargetsEnv, targetLocals,
      extremumBest, extremumSeen] using found
  obtain ⟨updated, yielded, _seen, best, _others⟩ :=
    BlockContinues.extremum_max_int (module := program) (globals := []) (heap := heap)
      (seen := false) (best := 0) (Evaluates.lookup valueFound) (by rfl) (by rfl)
  apply yielded.returns
  apply BlockReturns.range_done rfl
  apply BlockReturns.return_value
  exact Evaluates.lookup (by simpa using best)

theorem maximum_singleton.result (n : Int) (heap : Heap) :
    ReturnsValue program "maximum_singleton" [.scalar (.int n)] heap (.scalar (.int n)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact singleton_eval _ heap n rfl

theorem maximum_singleton.«Returns» (n : Int) :
    (HeapCalls.scalarFunction program "maximum_singleton" [.int n]).Returns :=
  ReturnsValue.scalar_returns (maximum_singleton.result n [])

theorem maximum_singleton.«Supported» (n : Int) :
    (HeapCalls.scalarFunction program "maximum_singleton" [.int n]).Supported :=
  (maximum_singleton.«Returns» n).supported

end tests.py.generator_extrema
