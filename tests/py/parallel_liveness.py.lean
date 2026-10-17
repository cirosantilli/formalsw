import «.formalsw».tests.py.«parallel_liveness.py.ast»
import FormalSW

open FormalSW.PyAst

namespace tests.py.parallel_liveness

private def pairWorker (first second : Nat) : ParallelWorker :=
  ⟨[.acquire (.name "first"), .yield, .acquire (.name "second"),
    .release (.name "second"), .release (.name "first")],
   [("first", .lock first), ("second", .lock second)]⟩

private theorem pair_source (first second : Nat) :
    parallelFunction ParallelLivenessAst.module "lock_pair" [.lock first, .lock second] =
      some (pairWorker first second) := by
  simp [parallelFunction, ParallelLivenessAst.module, findFunctionIn, executableBody, parallelOp, pairWorker]
  decide

private def retryWorker : ParallelWorker :=
  ⟨[.loop (.constant (.bool true))
      [.acquire (.name "mutex"), .release (.name "mutex"), .yield] []], [("mutex", .lock 0)]⟩

private theorem retry_source :
    parallelFunction ParallelLivenessAst.module "retry_forever" [.lock 0] = some retryWorker := by
  simp [parallelFunction, ParallelLivenessAst.module, findFunctionIn, executableBody, parallelOp, retryWorker]
  decide

private def opposite : ParallelConfig := ⟨⟨{}, [pairWorker 0 1, pairWorker 1 0]⟩, []⟩
private def stuck := (ParallelConfig.follow opposite [0, 1, 0, 1]).getD opposite
private def retries : ParallelConfig := ⟨⟨{}, [retryWorker, retryWorker]⟩, []⟩

private theorem infinite_retries : retries.CanDiverge := by
  exact ParallelConfig.canDiverge_of_follow (schedule := [0, 0, 0, 0, 1, 1, 1, 1]) (by decide) (by rfl)

theorem lock_pair.opposite_order_can_deadlock :
    let _this_module := ParallelLivenessAst.module;
    let this_function := FormalSW.PyAst.parallelFunction ParallelLivenessAst.module "lock_pair";
    CanDeadlock(Parallel([this_function [.lock 0, .lock 1],
                                this_function [.lock 1, .lock 0]], {}))
  := by
  dsimp only
  simp only [pair_source]
  exact ⟨opposite, stuck, rfl, ParallelConfig.reaches_of_follow (schedule := [0, 1, 0, 1]) (by rfl), rfl, rfl⟩

theorem lock_pair.opposite_order_not_halts :
    let _this_module := ParallelLivenessAst.module;
    let this_function := FormalSW.PyAst.parallelFunction ParallelLivenessAst.module "lock_pair";
    Not Halts(Parallel([this_function [.lock 0, .lock 1],
                              this_function [.lock 1, .lock 0]], {}))
  := by
  dsimp only
  intro halts
  exact ParallelRun.deadlockFree_not_canDeadlock
    (ParallelRun.halts_deadlockFree halts) lock_pair.opposite_order_can_deadlock

theorem lock_pair.same_order_returns :
    let _this_module := ParallelLivenessAst.module;
    let this_function := FormalSW.PyAst.parallelFunction ParallelLivenessAst.module "lock_pair";
    Returns(Parallel([this_function [.lock 0, .lock 1],
                            this_function [.lock 0, .lock 1]], {}))
  := by
  apply ParallelRun.Ensures.returns (post := fun _ => True)
  native_decide

theorem retry_forever.can_livelock :
    let _this_module := ParallelLivenessAst.module;
    let this_function := FormalSW.PyAst.parallelFunction ParallelLivenessAst.module "retry_forever";
    CanDiverge(Parallel([this_function [.lock 0], this_function [.lock 0]], {}))
  := by
  dsimp only
  simp only [retry_source]
  exact ⟨retries, rfl, infinite_retries⟩

theorem retry_forever.does_not_halt :
    let _this_module := ParallelLivenessAst.module;
    let this_function := FormalSW.PyAst.parallelFunction ParallelLivenessAst.module "retry_forever";
    Not Halts(Parallel([this_function [.lock 0], this_function [.lock 0]], {}))
  := by
  dsimp only
  intro halts
  exact ParallelRun.halts_not_canDiverge halts retry_forever.can_livelock

theorem retry_forever.quoted_can_livelock :
    python_context "tests/py/parallel_liveness.py" "retry_forever" ParallelLivenessAst.module in
    CanDiverge(py("run_retries(this_function, 2)"))
  := by
  refine ⟨rfl, _, rfl, retries, ?_, infinite_retries⟩
  simp only [retry_source]
  rfl

private def finishWorker : ParallelWorker :=
  ⟨[.acquire (.name "mutex"), .release (.name "mutex")], [("mutex", .lock 0)]⟩

private theorem finish_source :
    parallelFunction ParallelLivenessAst.module "finish" [.lock 0] = some finishWorker := by
  simp [parallelFunction, ParallelLivenessAst.module, findFunctionIn, executableBody, parallelOp, finishWorker]
  decide

theorem finish.quoted_returns :
    python_context "tests/py/parallel_liveness.py" "finish" ParallelLivenessAst.module in
    Returns(py("run_retries(this_function, 2)")) := by
  refine ⟨rfl, Or.inr ⟨_, rfl, ?_⟩⟩
  apply ParallelRun.Eventually.of_explore (fuel := 4) (state :=
    ⟨⟨{}, List.replicate 2 ⟨[.acquire (.name "mutex"), .release (.name "mutex")], [("mutex", .lock 0)]⟩⟩, []⟩)
  · simp only [finish_source]
    rfl
  · simp
  · simp
  · have observed : exploreParallel 4
        ⟨⟨{}, List.replicate 2 ⟨[.acquire (.name "mutex"), .release (.name "mutex")], [("mutex", .lock 0)]⟩⟩, []⟩ =
        [.ok {}, .ok {}] := by native_decide
    rw [observed]
    simp

theorem finish.quoted_halts :
    python_context "tests/py/parallel_liveness.py" "finish" ParallelLivenessAst.module in
    Halts(py("run_retries(this_function, 2)"))
  := by
  exact PyTrial.Call.returns_halts finish.quoted_returns

theorem finish.quoted_deadlock_free :
    python_context "tests/py/parallel_liveness.py" "finish" ParallelLivenessAst.module in
    DeadlockFree(py("run_retries(this_function, 2)"))
  := by
  exact PyTrial.Call.halts_deadlockFree finish.quoted_halts

private def twice : ParallelWorker :=
  ⟨[.acquire (.name "mutex"), .acquire (.name "mutex")], [("mutex", .lock 0)]⟩

private theorem twice_source :
    parallelFunction ParallelLivenessAst.module "acquire_twice" [.lock 0] = some twice := by
  simp [parallelFunction, ParallelLivenessAst.module, findFunctionIn, executableBody, parallelOp, twice]
  decide

theorem acquire_twice.can_deadlock :
    python_context "tests/py/parallel_liveness.py" "acquire_twice" ParallelLivenessAst.module in
    CanDeadlock(py("run_retries(this_function, 1)")) := by
  let initial : ParallelConfig := ⟨⟨{}, [twice]⟩, []⟩
  let stuck : ParallelConfig := ⟨⟨{ locked := [0] },
    [⟨[.acquire (.name "mutex")], [("mutex", .lock 0)]⟩]⟩, []⟩
  refine ⟨rfl, _, rfl, initial, stuck, ?_, ?_, rfl, rfl⟩
  · simp only [twice_source]
    rfl
  · exact ParallelConfig.reaches_of_follow (schedule := [0]) rfl

end tests.py.parallel_liveness
