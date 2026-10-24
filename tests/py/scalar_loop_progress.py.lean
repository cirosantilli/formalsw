import «.formalsw».tests.py.«scalar_loop_progress.py.ast»
import lang.py.FormalSW.LoopProgress

namespace tests.py.scalar_loop_progress
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := ScalarLoopProgressAst.module

/-- Every iteration increments an unbounded integer and reaches another supported loop boundary. -/
theorem spin_diverges (n : Int) : (Calls.function program "spin" [.int n]).Diverges := by
  let args := ((findFunctionIn program.body "spin").getD ([], [])).1
  let sourceBody := ((findFunctionIn program.body "spin").getD ([], [])).2
  let entry := argumentEnv args [.int n]
  let invariant : ScalarEnv → Prop := fun env => ∃ value : Int, env "n" = some (.int value)
  apply scalar_while_diverges program "spin" [.int n] args sourceBody []
    [.augAssign (.name "n") .add (.constant (.int 1))] rfl rfl rfl rfl invariant entry
  · exact BlockContinues.nil
  · exact ⟨n, rfl⟩
  · intro env current
    obtain ⟨value, found⟩ := current
    refine ⟨env.set "n" (.int (value + 1)), BlockContinues.augAssign ?_, value + 1, ?_⟩
    · exact Evaluates.binary (Evaluates.lookup found) Evaluates.constant rfl
    · simp [ScalarEnv.set]

end tests.py.scalar_loop_progress
