import lang.py.CleanXY.Parallel

/-! Unbounded liveness for a joined concurrent batch. All choices of enabled
workers are included. There are no idle scheduler steps or fairness axioms.
A finite stuck execution and an infinite execution are distinct witnesses. -/
namespace CleanXY.PyAst

namespace ParallelConfig

inductive Reaches : ParallelConfig → ParallelConfig → Prop where
  | refl {state : ParallelConfig} : Reaches state state
  | step {state next final : ParallelConfig} : next ∈ state.next → Reaches next final → Reaches state final

/-- Global deadlock: unfinished workers remain, and none can take a step. -/
def Deadlocked (state : ParallelConfig) : Prop := state.finished = false ∧ state.next = []

/-- Inductive total correctness over every enabled scheduling choice. -/
inductive MustFinish (accept : ParallelOutcome → Prop) : ParallelConfig → Prop where
  | done {state : ParallelConfig} : state.finished = true → accept state.outcome → MustFinish accept state
  | step {state : ParallelConfig} : state.finished = false → state.next ≠ [] →
      (∀ next ∈ state.next, MustFinish accept next) → MustFinish accept state

/-- An infinite path, witnessed by a nonempty successor-closed set. Existential
successors express a possible scheduling choice, not all choices. -/
def CanDiverge (state : ParallelConfig) : Prop :=
  ∃ invariant : ParallelConfig → Prop, invariant state ∧
    ∀ current, invariant current → ∃ next ∈ current.next, invariant next

variable {state next final : ParallelConfig} {p q : ParallelOutcome → Prop}

theorem finished_next_empty (state : ParallelConfig) (h : state.finished = true) : state.next = [] := by
  simp only [finished, List.all_eq_true] at h
  apply List.filterMap_eq_nil_iff.mpr
  intro index member
  have bound := List.mem_range.mp member
  have empty := h _ (List.getElem_mem bound)
  have todo : state.state.workers[index].todo = [] := List.isEmpty_iff.mp empty
  simp [parallelChoose, List.getElem?_eq_getElem bound, parallelStep, todo]

theorem MustFinish.mono (h : MustFinish p state) (f : ∀ o, p o → q o) : MustFinish q state := by
  induction h with
  | done finished accepted => exact .done finished (f _ accepted)
  | step unfinished enabled _ ih => exact .step unfinished enabled ih

theorem MustFinish.after (h : MustFinish p state) (member : next ∈ state.next) : MustFinish p next := by
  cases h with
  | done finished _ => simp [finished_next_empty state finished] at member
  | step _ _ children => exact children next member

theorem MustFinish.reaches (h : MustFinish p state) (path : Reaches state final) : MustFinish p final := by
  induction path with
  | refl => exact h
  | step edge _ ih => exact ih (h.after edge)

theorem MustFinish.not_deadlocked (h : MustFinish p state) : ¬ state.Deadlocked := by
  rintro ⟨unfinished, empty⟩
  cases h with
  | done finished _ => simp [unfinished] at finished
  | step _ enabled _ => exact enabled empty

theorem MustFinish.not_diverge (h : MustFinish p state) : ¬ state.CanDiverge := by
  rintro ⟨invariant, initial, advance⟩
  induction h with
  | done finished _ =>
      obtain ⟨next, edge, _⟩ := advance _ initial
      simp [finished_next_empty _ finished] at edge
  | step _ _ _ ih =>
      obtain ⟨next, edge, preserved⟩ := advance _ initial
      exact ih next edge preserved

theorem MustFinish.accepts (h : MustFinish p state) (finished : state.finished = true) : p state.outcome := by
  cases h with
  | done _ accepted => exact accepted
  | step unfinished _ _ => simp [finished] at unfinished

/-- A completely explored finite tree is a sound termination certificate.
No inference is made from an exhausted budget. -/
theorem mustFinish_of_explore (rejectIncomplete : ¬ p (.error .incomplete))
    (rejectDeadlock : ¬ p (.error .deadlock))
    (h : ∀ o ∈ exploreParallel fuel state, p o) : MustFinish p state := by
  induction fuel generalizing state with
  | zero =>
      cases finished : state.finished with
      | true => exact .done finished (h _ (by simp [exploreParallel, finished]))
      | false => exact False.elim (rejectIncomplete (h _ (by simp [exploreParallel, finished])))
  | succ fuel ih =>
      cases finished : state.finished with
      | true => exact .done finished (h _ (by simp [exploreParallel, finished]))
      | false =>
          by_cases empty : state.next = []
          · exact False.elim (rejectDeadlock (h _ (by simp [exploreParallel, finished, empty])))
          · apply MustFinish.step finished empty
            intro next member
            apply ih
            intro outcome found
            exact h outcome (by simp only [exploreParallel, finished, Bool.false_eq_true, ↓reduceIte,
              List.isEmpty_eq_false_iff.mpr empty]; exact List.mem_flatMap.mpr ⟨next, member, found⟩)

def follow (state : ParallelConfig) : List Nat → Option ParallelConfig
  | [] => some state
  | index :: rest => do follow (← parallelChoose state index) rest

theorem chosen_mem (h : parallelChoose state index = some next) : next ∈ state.next := by
  have bound : index < state.state.workers.length := by
    by_cases bound : index < state.state.workers.length
    · exact bound
    have missing : state.state.workers[index]? = none := List.getElem?_eq_none (by omega)
    simp [parallelChoose, missing] at h
  exact List.mem_filterMap.mpr ⟨index, List.mem_range.mpr bound, h⟩

theorem reaches_of_follow (h : follow state schedule = some final) : Reaches state final := by
  induction schedule generalizing state with
  | nil => simp [follow] at h; subst final; exact .refl
  | cons index rest ih =>
      cases chosen : parallelChoose state index with
      | none => simp [follow, chosen] at h
      | some next => exact .step (chosen_mem chosen) (ih (by simpa [follow, chosen] using h))

theorem canDiverge_of_cycle (edge : next ∈ state.next) (back : Reaches next state) : state.CanDiverge := by
  refine ⟨fun current => Reaches current state, .refl, ?_⟩
  intro current path
  cases path with
  | refl => exact ⟨next, edge, back⟩
  | step first rest => exact ⟨_, first, rest⟩

theorem canDiverge_of_follow (nonempty : schedule ≠ []) (cycle : follow state schedule = some state) :
    state.CanDiverge := by
  cases schedule with
  | nil => exact False.elim (nonempty rfl)
  | cons index rest =>
      cases chosen : parallelChoose state index with
      | none => simp [follow, chosen] at cycle
      | some next =>
          exact canDiverge_of_cycle (chosen_mem chosen)
            (reaches_of_follow (by simpa [follow, chosen] using cycle))

theorem Reaches.invariant (path : Reaches state final) {invariant : ParallelConfig → Prop}
    (initial : invariant state)
    (preserve : ∀ current next, invariant current → next ∈ current.next → invariant next) :
    invariant final := by
  induction path with
  | refl => exact initial
  | step edge _ ih => exact ih (preserve _ _ initial edge)

theorem CanDiverge.before (h : next.CanDiverge) (edge : next ∈ state.next) : state.CanDiverge := by
  obtain ⟨invariant, initial, advance⟩ := h
  refine ⟨fun current => current = state ∨ invariant current, Or.inl rfl, ?_⟩
  rintro current (rfl | member)
  · exact ⟨next, edge, Or.inr initial⟩
  · obtain ⟨after, step, preserved⟩ := advance current member
    exact ⟨after, step, Or.inr preserved⟩

theorem CanDiverge.of_reaches (h : final.CanDiverge) (path : Reaches state final) : state.CanDiverge := by
  induction path with
  | refl => exact h
  | step edge _ ih => exact (ih h).before edge

theorem MustFinish.strengthen (h : MustFinish p state)
    (check : ∀ final, Reaches state final → final.finished = true → q final.outcome) : MustFinish q state := by
  induction h with
  | done finished _ => exact .done finished (check _ .refl finished)
  | step unfinished nonempty _ ih =>
      apply MustFinish.step unfinished nonempty
      intro next edge
      exact ih next edge (fun final path done => check final (.step edge path) done)

end ParallelConfig

namespace ParallelRun

variable {run : ParallelRun} {state : ParallelConfig} {p : ParallelOutcome → Prop}

def Eventually (run : ParallelRun) (accept : ParallelOutcome → Prop) : Prop :=
  ∃ state, run.config = some state ∧ state.MustFinish accept

def Halts (run : ParallelRun) : Prop := run.Eventually fun
  | .ok _ | .error (.exception _) => True
  | _ => False

def Returns (run : ParallelRun) : Prop := run.Eventually fun
  | .ok _ => True
  | _ => False

def Throws (run : ParallelRun) : Prop :=
  ∃ initial final exception, run.config = some initial ∧ initial.Reaches final ∧
    final.finished = true ∧ final.outcome = .error (.exception exception)

def CanDeadlock (run : ParallelRun) : Prop :=
  ∃ initial final, run.config = some initial ∧ initial.Reaches final ∧ final.Deadlocked

def DeadlockFree (run : ParallelRun) : Prop :=
  ∃ initial, run.config = some initial ∧ ∀ final, initial.Reaches final → ¬ final.Deadlocked

def CanDiverge (run : ParallelRun) : Prop :=
  ∃ initial, run.config = some initial ∧ initial.CanDiverge

theorem returns_halts (h : run.Returns) : run.Halts := by
  obtain ⟨state, source, done⟩ := h
  refine ⟨state, source, done.mono ?_⟩
  intro o ho
  cases o with
  | ok _ => trivial
  | error e => contradiction

theorem halts_deadlockFree (h : run.Halts) : run.DeadlockFree := by
  obtain ⟨state, source, done⟩ := h
  exact ⟨state, source, fun _ path => (done.reaches path).not_deadlocked⟩

theorem deadlockFree_not_canDeadlock (h : run.DeadlockFree) : ¬ run.CanDeadlock := by
  rintro ⟨initial, final, source, path, stuck⟩
  obtain ⟨state, other, safe⟩ := h
  have eq := Option.some.inj (other.symm.trans source)
  subst initial
  exact safe _ path stuck

theorem halts_not_canDiverge (h : run.Halts) : ¬ run.CanDiverge := by
  rintro ⟨initial, source, infinite⟩
  obtain ⟨state, other, done⟩ := h
  have eq := Option.some.inj (other.symm.trans source)
  subst initial
  exact done.not_diverge infinite

theorem returns_not_throws (h : run.Returns) : ¬ run.Throws := by
  rintro ⟨initial, final, exception, source, path, finished, outcome⟩
  obtain ⟨state, other, done⟩ := h
  have eq := Option.some.inj (other.symm.trans source)
  subst initial
  have accepted := (done.reaches path).accepts finished
  simp [outcome] at accepted

theorem returns_iff_halts_not_throws : run.Returns ↔ run.Halts ∧ ¬ run.Throws := by
  constructor
  · intro returned
    exact ⟨returns_halts returned, returns_not_throws returned⟩
  · rintro ⟨⟨state, source, done⟩, noThrow⟩
    refine ⟨state, source, done.strengthen ?_⟩
    intro final path finished
    have supported := (done.reaches path).accepts finished
    cases outcome : final.outcome with
    | ok value => trivial
    | error error =>
        cases error <;> simp_all
        exact noThrow ⟨state, final, _, source, path, finished, outcome⟩

theorem Eventually.of_explore {run : ParallelRun} (source : run.config = some state)
    (rejectIncomplete : ¬ p (.error .incomplete)) (rejectDeadlock : ¬ p (.error .deadlock))
    (h : ∀ o ∈ exploreParallel fuel state, p o) : run.Eventually p :=
  ⟨state, source, ParallelConfig.mustFinish_of_explore rejectIncomplete rejectDeadlock h⟩

/-- Existing finite guarantees also prove unbounded successful termination. -/
theorem Ensures.returns (h : run.Ensures post) : run.Returns := by
  cases source : run.config with
  | none =>
      have bad := h.2 (.error .unsupported) (by simp [outcomes, source])
      contradiction
  | some state =>
      apply Eventually.of_explore source (by simp) (by simp)
      intro o member
      have good := h.2 o (by simpa [outcomes, source] using member)
      cases o with
      | ok _ => trivial
      | error e => contradiction

end ParallelRun

macro "CanDeadlock(" run:term ")" : term => `(($run).CanDeadlock)
macro "DeadlockFree(" run:term ")" : term => `(($run).DeadlockFree)
macro "CanDiverge(" run:term ")" : term => `(($run).CanDiverge)
macro "Halts(" "Parallel(" calls:term "," state:term ")" ")" : term =>
  `((parallelRun $calls $state).Halts)
macro "Returns(" "Parallel(" calls:term "," state:term ")" ")" : term =>
  `((parallelRun $calls $state).Returns)
macro "Throws(" "Parallel(" calls:term "," state:term ")" ")" : term =>
  `((parallelRun $calls $state).Throws)

end CleanXY.PyAst
