import FormalSW
open FormalSW.PyAst

-- Exhausted observation fuel is not a proof of nontermination.
private def countdown : ParallelWorker :=
  ⟨[.loop (.compare (.name "n") [(.gt, .constant (.int 0))])
      [.assign "n" (.binOp (.name "n") .sub (.constant (.int 1)))] []], [("n", .int 5)]⟩
private def countdownRun := parallelRun [some countdown] {}
example : countdownRun.outcomes = [.error .incomplete] := by native_decide
example : countdownRun.Returns := by
  apply ParallelRun.Eventually.of_explore (state := ⟨⟨{}, [countdown]⟩, []⟩)
    (fuel := 11) rfl (by simp) (by simp)
  have observed : exploreParallel 11 ⟨⟨{}, [countdown]⟩, []⟩ = [.ok {}] := by native_decide
  rw [observed]
  simp

example : Returns(Parallel([], {})) := ⟨⟨⟨{}, []⟩, []⟩, rfl, .done rfl trivial⟩
example : ¬ (parallelRun [none] {}).Halts := by
  rintro ⟨state, source, _⟩
  cases source

-- While-else and branches execute their actual selected body.
example : exploreParallel 3 ⟨⟨{}, [⟨[.loop (.constant (.bool false)) []
    [.branch (.constant (.bool true)) [.yield] []]], []⟩]⟩, []⟩ = [.ok {}] := by native_decide

-- An infinite execution need not revisit the same state. This worker keeps
-- increasing an unbounded integer; its invariant includes both control points.
private def addOne := ParallelOp.assign "n" (.binOp (.name "n") .add (.constant (.int 1)))
private def grow := ParallelOp.loop (.constant (.bool true)) [addOne] []
private def growing (n : Int) (env : SharedEnv) (body : Bool) : ParallelConfig :=
  ⟨⟨{}, [⟨if body then [addOne, grow] else [grow], ("n", .int n) :: env⟩]⟩, []⟩

example : (growing 0 [] false).CanDiverge := by
  refine ⟨fun state => ∃ n env, state = growing n env false ∨ state = growing n env true,
    ⟨0, [], Or.inl rfl⟩, ?_⟩
  rintro current ⟨n, env, rfl | rfl⟩
  · exact ⟨growing n env true, ParallelConfig.chosen_mem (index := 0) rfl, n, env, Or.inr rfl⟩
  · exact ⟨growing (n + 1) (("n", .int n) :: env) false,
      ParallelConfig.chosen_mem (index := 0) rfl, n + 1, ("n", .int n) :: env, Or.inl rfl⟩

private def forever : ParallelWorker := ⟨[.loop (.constant (.bool true)) [.yield] []], []⟩
private def raises : ParallelWorker := ⟨[.release (.name "mutex")], [("mutex", .lock 0)]⟩
private def mixed : ParallelConfig := ⟨⟨{}, [raises, forever]⟩, []⟩
private def afterError : ParallelConfig :=
  ⟨⟨{}, [⟨[], [("mutex", .lock 0)]⟩, forever]⟩, [.exception ⟨"RuntimeError", []⟩]⟩

-- A joined batch cannot halt just because one future raises. The remaining
-- worker continues, so the caller remains in the executor's shutdown/join.
private theorem mixed_diverges : mixed.CanDiverge := by
  have infinite : afterError.CanDiverge :=
    ParallelConfig.canDiverge_of_follow (schedule := [1, 1]) (by decide) (by rfl)
  exact infinite.before (ParallelConfig.chosen_mem (index := 0) rfl)

example : ¬ (parallelRun [some raises, some forever] {}).Halts := by
  intro done
  exact ParallelRun.halts_not_canDiverge done ⟨mixed, rfl, mixed_diverges⟩

-- An exception does count as termination once all workers really finish.
private def failed : ParallelConfig := ⟨⟨{}, [⟨[], [("mutex", .lock 0)]⟩]⟩,
    [.exception ⟨"RuntimeError", []⟩]⟩
example : Throws(Parallel([some raises], {})) :=
  ⟨⟨⟨{}, [raises]⟩, []⟩, failed, ⟨"RuntimeError", []⟩, rfl,
   ParallelConfig.reaches_of_follow (schedule := [0]) rfl, rfl, rfl⟩
example : Halts(Parallel([some raises], {})) := by
  apply ParallelRun.Eventually.of_explore (state := ⟨⟨{}, [raises]⟩, []⟩) (fuel := 1)
    rfl (by simp) (by simp)
  have observed : exploreParallel 1 ⟨⟨{}, [raises]⟩, []⟩ = [.error (.exception ⟨"RuntimeError", []⟩)] := rfl
  rw [observed]
  simp

-- The optimized mutex certificate must not erase locks hidden in control flow.
example : Mutex.extract ⟨[.acquire (.name "mutex"),
    .loop (.constant (.bool true)) [.acquire (.name "mutex")] [],
    .release (.name "mutex")], [("mutex", .lock 0)]⟩ = none := rfl

-- Deadlock freedom alone does not imply termination: this worker always has
-- another enabled step, and yet never completes.
private def spinning : ParallelConfig := ⟨⟨{}, [forever]⟩, []⟩
private def yielding : ParallelConfig :=
  ⟨⟨{}, [⟨[.yield, .loop (.constant (.bool true)) [.yield] []], []⟩]⟩, []⟩

private theorem spin_reachable {final : ParallelConfig} (path : spinning.Reaches final) :
    final = spinning ∨ final = yielding := by
  apply path.invariant (Or.inl rfl)
  rintro current next (rfl | rfl) edge
  · have step : spinning.next = [yielding] := rfl
    rw [step] at edge
    exact Or.inr (List.mem_singleton.mp edge)
  · have step : yielding.next = [spinning] := rfl
    rw [step] at edge
    exact Or.inl (List.mem_singleton.mp edge)

example : DeadlockFree(Parallel([some forever], {})) := by
  refine ⟨spinning, rfl, ?_⟩
  intro final path
  rcases spin_reachable path with rfl | rfl
  · intro stuck
    have step : spinning.next = [yielding] := rfl
    exact List.cons_ne_nil _ _ (step.symm.trans stuck.2)
  · intro stuck
    have step : yielding.next = [spinning] := rfl
    exact List.cons_ne_nil _ _ (step.symm.trans stuck.2)

example : CanDiverge(Parallel([some forever], {})) :=
  ⟨spinning, rfl, ParallelConfig.canDiverge_of_follow (schedule := [0, 0]) (by decide) rfl⟩

example : ¬ Throws(Parallel([some forever], {})) := by
  rintro ⟨initial, final, _, source, path, finished, _⟩
  have same : initial = spinning := Option.some.inj source.symm
  subst initial
  rcases spin_reachable path with rfl | rfl <;> cases finished

-- An internal coverage failure cannot be hidden by a preceding exception.
example : (⟨⟨{}, []⟩, [.exception ⟨"RuntimeError", []⟩, .unsupported]⟩ : ParallelConfig).outcome =
    .error .unsupported := rfl

-- A failure while holding a lock can also leave the joined batch deadlocked.
private def failsHoldingLock : ParallelWorker :=
  ⟨[.acquire (.name "first"), .release (.name "second")],
    [("first", .lock 0), ("second", .lock 1)]⟩
private def waitsForLock : ParallelWorker :=
  ⟨[.acquire (.name "mutex")], [("mutex", .lock 0)]⟩
private def failedAndBlocked := parallelRun [some failsHoldingLock, some waitsForLock] {}
private theorem failure_deadlock : failedAndBlocked.CanDeadlock := by
  let initial : ParallelConfig := ⟨⟨{}, [failsHoldingLock, waitsForLock]⟩, []⟩
  let final : ParallelConfig := ⟨⟨{ locked := [0] },
    [⟨[], [("first", .lock 0), ("second", .lock 1)]⟩, waitsForLock]⟩,
    [.exception ⟨"RuntimeError", []⟩]⟩
  exact ⟨initial, final, rfl, ParallelConfig.reaches_of_follow (schedule := [0, 0]) rfl, rfl, rfl⟩
example : ¬ failedAndBlocked.Halts := by
  intro halted
  exact ParallelRun.deadlockFree_not_canDeadlock (ParallelRun.halts_deadlockFree halted) failure_deadlock
