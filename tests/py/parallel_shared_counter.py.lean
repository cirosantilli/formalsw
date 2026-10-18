import «.formalsw».tests.py.«parallel_shared_counter.py.ast»
import FormalSW

open FormalSW.PyAst

namespace tests.py.parallel_shared_counter

namespace CounterProof

private def heap (head : Int) (tail : List Int) : SharedState :=
  { objects := [.array ((head :: tail).map SharedValue.int)] }

private def worker : ParallelWorker :=
  ⟨[.read "snapshot" (.item (.name "counter") (.constant (.int 0))),
    .yield,
    .write (.item (.name "counter") (.constant (.int 0)))
      (.binOp (.name "snapshot") .add (.constant (.int 1)))],
   [("counter", .ref 0), ("mutex", .lock 0)]⟩

private theorem executes (head : Int) (tail : List Int) :
    Mutex.execute worker.todo worker.locals (heap head tail) = some (heap (head + 1) tail) := by
  rfl

private theorem repeated (count : Nat) (head : Int) (tail : List Int) :
    Mutex.Ensures (fun final => final = heap (head + count) tail)
      (List.replicate count worker) none (heap head tail) := by
  let I := fun (pending : List ParallelWorker) (state : SharedState) => ∃ current : Int,
    state = heap current tail ∧ current + (pending.length : Int) = head + count ∧
    ∀ w ∈ pending, w = worker
  apply Mutex.invariant I
  · rintro state ⟨current, rfl, total, _⟩
    simp only [List.length_nil, Int.natCast_zero, Int.add_zero] at total
    rw [total]
  · rintro before selected after state ⟨current, rfl, total, same⟩
    have selected_eq := same selected (by simp)
    subst selected
    refine ⟨heap (current + 1) tail, executes current tail, current + 1, rfl, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, Int.natCast_add, Int.natCast_succ] at total ⊢
      omega
    · intro w member
      apply same w
      rcases List.mem_append.mp member with h | h
      · simp [h]
      · simp [h]
  · exact ⟨head, rfl, by simp, by intro w member; exact (List.mem_replicate.mp member).2⟩

private def trial (name : String) (values : List Int) (count : Int) : PyTrial :=
  { calls := List.replicate count.toNat
      (parallelFunction ParallelSharedCounterAst.module name [.ref 0, .lock 0])
    initial := { objects := [.array (values.map .int)] }
    check := fun final => do
      PyTrial.assertTrue ((← PyTrial.readIntItem final 0 0) == ((← PyTrial.intItem values 0) + count))
      PyTrial.assertTrue (((← PyTrial.readInts final 0).drop 1) == values.drop 1)
      pure () }

private theorem safe_source :
    parallelFunction ParallelSharedCounterAst.module "increment_safe" [.ref 0, .lock 0] =
      some ⟨[ParallelOp.acquire (.name "mutex")] ++ worker.todo ++ [ParallelOp.release (.name "mutex")], worker.locals⟩ := by
  simp [parallelFunction, ParallelSharedCounterAst.module, findFunctionIn, executableBody, parallelOp, sharedLocation, worker]
  decide

private theorem extracted (count : Nat) :
    (List.replicate count (parallelFunction ParallelSharedCounterAst.module "increment_safe" [.ref 0, .lock 0])).mapM
      (fun call => do
        let (identity, worker) ← Mutex.extract (← call)
        if identity = 0 then some worker else none) = some (List.replicate count worker) := by
  simp only [safe_source]
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.mapM_cons]
      change ((List.replicate count (some (⟨[ParallelOp.acquire (.name "mutex")] ++ worker.todo ++ [ParallelOp.release (.name "mutex")], worker.locals⟩ : ParallelWorker))).mapM
        (fun call => do let (identity, worker) ← Mutex.extract (← call); if identity = 0 then some worker else none)).bind
        (fun rest => some (worker :: rest)) = some (worker :: List.replicate count worker)
      rw [ih]
      rfl

private theorem all_updates (head : Int) (tail : List Int) (count : Int) (nonnegative : 0 ≤ count) :
    PyTrial.Returns (some (trial "increment_safe" (head :: tail) count)) := by
  apply Or.inl
  refine ⟨_, rfl, 0, List.replicate count.toNat worker, rfl, extracted count.toNat, ?_⟩
  apply (repeated count.toNat head tail).mono
  intro final equal
  subst final
  simp only [Int.toNat_of_nonneg nonnegative]
  change (do
    PyTrial.assertTrue ((← PyTrial.readIntItem (heap (head + count) tail) 0 0) == ((← PyTrial.intItem (head :: tail) 0) + count))
    PyTrial.assertTrue (((← PyTrial.readInts (heap (head + count) tail) 0).drop 1) == (head :: tail).drop 1)
    pure ()) = some ()
  have read : PyTrial.readInts (heap (head + count) tail) 0 = some ((head + count) :: tail) := by
    unfold PyTrial.readInts heap
    simp only [List.map_cons, List.getElem?_cons_zero]
    have conversion : ∀ xs : List Int, (xs.map SharedValue.int).mapM
        (fun | .int n => some n | _ => none) = some xs := by
      intro xs
      induction xs with
      | nil => rfl
      | cons n xs ih => simp only [List.map_cons, List.mapM_cons]; simp [ih]
    simpa using conversion ((head + count) :: tail)
  rw [read]
  change (do PyTrial.assertTrue ((head + count) == (head + count)); PyTrial.assertTrue (tail == tail); pure ()) = some ()
  simp [PyTrial.assertTrue]

private def valid (counter worker_count : PyValue) : Prop :=
  python_context "tests/py/parallel_shared_counter.py" "increment_safe" ParallelSharedCounterAst.module in
    py("valid_trial_input(counter, worker_count)")

private theorem valid_domain (counter worker_count : PyValue) (h : valid counter worker_count) :
    ∃ (head : Int) (tail : List Int) (count : Int),
      counter = .list ((head :: tail).map .int) ∧ worker_count = .int count ∧ 0 ≤ count := by
  change PyValue.andThen (PyValue.typeIs counter "list") (fun _ =>
    PyValue.andThen (counter.length.bind (fun n => PyValue.compare .gt n (.int 0))) (fun _ =>
    PyValue.andThen (PyValue.all (fun value => PyValue.typeIs value "int") counter) (fun _ =>
    PyValue.andThen (PyValue.typeIs worker_count "int") (fun _ =>
    PyValue.compare .gtE worker_count (.int 0))))) = some (.bool true) at h
  simp only [PyValue.andThen_true, PyValue.typeIs_list, PyValue.typeIs_int] at h
  rcases h with ⟨⟨values, rfl⟩, length, elements, ⟨count, rfl⟩, nonnegative⟩
  obtain ⟨integers, rfl⟩ := PyValue.ints_of_all values elements
  simp [PyValue.compare, PyValue.asInt] at nonnegative
  cases integers with
  | nil => simp [PyValue.length, PyValue.compare, PyValue.asInt] at length
  | cons head tail => exact ⟨head, tail, count, rfl, rfl, nonnegative⟩

end CounterProof

theorem increment_unsafe.loses_an_update :
    python_context "tests/py/parallel_shared_counter.py" "increment_unsafe" ParallelSharedCounterAst.module in
    ∃ (counter worker_count : PyValue),
            py("valid_trial_input(counter, worker_count)") ∧
            Throws(py("run_trial(this_function, counter, worker_count)"))
  := by
  refine ⟨.list [.int 0], .int 2, ?_, ?_⟩
  · rfl
  · apply Or.inr
    refine ⟨rfl, Or.inl ⟨_, rfl, Or.inr ⟨{ objects := [.array [.int 1]] }, ?_, ?_⟩⟩⟩
    · native_decide
    · decide

theorem increment_safe.preserves_updates :
    python_context "tests/py/parallel_shared_counter.py" "increment_safe" ParallelSharedCounterAst.module in
    ∀ (counter worker_count : PyValue),
            py("valid_trial_input(counter, worker_count)") →
            Returns(py("run_trial(this_function, counter, worker_count)"))
  := by
  intro counter worker_count valid
  refine ⟨valid, ?_⟩
  obtain ⟨head, tail, count, rfl, rfl, nonnegative⟩ := CounterProof.valid_domain counter worker_count valid
  dsimp only [Bind.bind, Option.bind]
  rw [PyValue.asInts_ints]
  dsimp only [Bind.bind, Option.bind, PyValue.asInt]
  simpa only [List.length_map, List.length_range] using CounterProof.all_updates head tail count nonnegative

theorem increment_unsafe.returns :
    let _this_module := ParallelSharedCounterAst.module;
    let this_function := parallelFunction ParallelSharedCounterAst.module "increment_unsafe";
    ∀ (head : Int) (tail : List Int),
      Returns(Parallel([this_function [.ref 0, .lock 0]],
        { objects := [.array ((head :: tail).map SharedValue.int)] })) := by
  dsimp only
  intro head tail
  apply ParallelRun.Ensures.returns (post := fun _ => True)
  have outcomes :
      (parallelRun [parallelFunction ParallelSharedCounterAst.module "increment_unsafe" [.ref 0, .lock 0]]
        { objects := [.array ((head :: tail).map SharedValue.int)] }).outcomes =
      [.ok { objects := [.array (((head + 1) :: tail).map SharedValue.int)] }] := by
    cbv
  constructor
  · rw [outcomes]; simp
  · rw [outcomes]; simp

set_option maxHeartbeats 800000 in
theorem increment_safe.returns :
    let _this_module := ParallelSharedCounterAst.module;
    let this_function := parallelFunction ParallelSharedCounterAst.module "increment_safe";
    ∀ (head : Int) (tail : List Int),
      Returns(Parallel([this_function [.ref 0, .lock 0]],
        { objects := [.array ((head :: tail).map SharedValue.int)] })) := by
  dsimp only
  intro head tail
  apply ParallelRun.Ensures.returns (post := fun _ => True)
  have outcomes :
      (parallelRun [parallelFunction ParallelSharedCounterAst.module "increment_safe" [.ref 0, .lock 0]]
        { objects := [.array ((head :: tail).map SharedValue.int)] }).outcomes =
      [.ok { objects := [.array (((head + 1) :: tail).map SharedValue.int)] }] := by
    rw [CounterProof.safe_source]
    cbv
  constructor
  · rw [outcomes]; simp
  · rw [outcomes]; simp

end tests.py.parallel_shared_counter
