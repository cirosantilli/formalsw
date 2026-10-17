import lang.py.CleanXY.Model

/-! Deterministic transition systems. Termination requires a finite derivation;
running out of observation fuel never manufactures a return value. -/

namespace CleanXY.PyAst

inductive Step (σ α : Type) where
  | next (state : σ)
  | done (outcome : Except ExceptionObject α)
  | unsupported

/-- A computation can take arbitrarily many steps, finish, or reach unsupported code. -/
structure Execution (α : Type) where
  State : Type
  initial : State
  step : State → Step State α

inductive Finishes (step : σ → Step σ α) : σ → Except ExceptionObject α → Prop where
  | done (h : step state = .done outcome) : Finishes step state outcome
  | next (h : step state = .next following) (rest : Finishes step following outcome) :
      Finishes step state outcome

namespace Finishes

theorem unique (left : Finishes step state a) (right : Finishes step state b) : a = b := by
  induction left with
  | done h =>
      cases right with
      | done h' => simpa [h] using h'
      | next h' _ => simp [h] at h'
  | next h _ ih =>
      cases right with
      | done h' => simp [h] at h'
      | next h' rest =>
          simp only [h, Step.next.injEq] at h'
          subst h'
          exact ih rest

end Finishes

namespace Execution

def Halts (execution : Execution α) : Prop :=
  ∃ outcome, Finishes execution.step execution.initial outcome

def Returns (execution : Execution α) : Prop :=
  ∃ value, Finishes execution.step execution.initial (.ok value)

def Throws (execution : Execution α) : Prop :=
  ∃ exception, Finishes execution.step execution.initial (.error exception)

/-- A supported infinite execution, witnessed by an invariant closed under steps.
Unsupported code is not divergence: the invariant must always produce a next step. -/
def Diverges (execution : Execution α) : Prop :=
  ∃ invariant : execution.State → Prop,
    invariant execution.initial ∧
    ∀ state, invariant state →
      ∃ following, execution.step state = .next following ∧ invariant following

theorem throws_halts {execution : Execution α} (h : execution.Throws) : execution.Halts := by
  obtain ⟨exception, h⟩ := h
  exact ⟨.error exception, h⟩

theorem returns_iff_halts_not_throws (execution : Execution α) :
    execution.Returns ↔ execution.Halts ∧ ¬ execution.Throws := by
  constructor
  · rintro ⟨value, h⟩
    refine ⟨⟨.ok value, h⟩, ?_⟩
    rintro ⟨exception, thrown⟩
    have := h.unique thrown
    contradiction
  · rintro ⟨⟨outcome, h⟩, safe⟩
    cases outcome with
    | ok value => exact ⟨value, h⟩
    | error exception => exact False.elim (safe ⟨exception, h⟩)

theorem diverges_not_halts {execution : Execution α} (h : execution.Diverges) :
    ¬ execution.Halts := by
  obtain ⟨invariant, initial, closed⟩ := h
  rintro ⟨outcome, finished⟩
  have impossible : ∀ state outcome, Finishes execution.step state outcome →
      invariant state → False := by
    intro state outcome finished
    induction finished with
    | done h =>
        intro initial
        obtain ⟨_, next, _⟩ := closed _ initial
        simp [h] at next
    | next h _ ih =>
        intro initial
        obtain ⟨following, next, preserved⟩ := closed _ initial
        simp only [h, Step.next.injEq] at next
        subst following
        exact ih preserved
  exact impossible _ _ finished initial

def pure (value : α) : Execution α := ⟨Unit, (), fun _ => .done (.ok value)⟩
def raise (exception : ExceptionObject) : Execution α :=
  ⟨Unit, (), fun _ => .done (.error exception)⟩
def unsupported : Execution α := ⟨Unit, (), fun _ => .unsupported⟩

def ofExcept (outcome : Except ExceptionObject α) : Execution α :=
  ⟨Unit, (), fun _ => .done outcome⟩

/-- Adapter for legacy partial evaluators. `none` remains unsupported, not divergent. -/
def ofOption (outcome : Option (Except ExceptionObject α)) : Execution α :=
  match outcome with
  | some outcome => ofExcept outcome
  | none => unsupported

def bind (execution : Execution α) (continuation : α → Execution β) : Execution β where
  State := Sum execution.State (Sigma fun value => (continuation value).State)
  initial := .inl execution.initial
  step
    | .inl state =>
        match execution.step state with
        | .next following => .next (.inl following)
        | .done (.ok value) => .next (.inr ⟨value, (continuation value).initial⟩)
        | .done (.error exception) => .done (.error exception)
        | .unsupported => .unsupported
    | .inr ⟨value, state⟩ =>
        match (continuation value).step state with
        | .next following => .next (.inr ⟨value, following⟩)
        | .done outcome => .done outcome
        | .unsupported => .unsupported

theorem finishes_bind_right {execution : Execution α} {continuation : α → Execution β}
    {value : α} {state : (continuation value).State} {outcome : Except ExceptionObject β}
    (h : Finishes (continuation value).step state outcome) :
    Finishes (execution.bind continuation).step (.inr ⟨value, state⟩) outcome := by
  induction h with
  | done h => exact .done (by simp [bind, h])
  | next h _ ih => exact .next (by simp [bind, h]) ih

theorem finishes_bind_ok {execution : Execution α} {continuation : α → Execution β}
    {value : α} {state : execution.State} {outcome : Except ExceptionObject β}
    (h : Finishes execution.step state (.ok value))
    (rest : Finishes (continuation value).step (continuation value).initial outcome) :
    Finishes (execution.bind continuation).step (.inl state) outcome := by
  generalize result_eq : Except.ok value = result at h
  induction h with
  | done h =>
      cases result_eq
      exact .next (by simp [bind, h]) (finishes_bind_right rest)
  | next h _ ih => exact .next (by simp [bind, h]) (ih result_eq)

theorem returns_bind {execution : Execution α} {continuation : α → Execution β}
    (h : Finishes execution.step execution.initial (.ok value))
    (rest : (continuation value).Returns) : (execution.bind continuation).Returns := by
  obtain ⟨result, rest⟩ := rest
  exact ⟨result, finishes_bind_ok h rest⟩

theorem returns_pure (value : α) : (pure value).Returns := ⟨value, .done rfl⟩

private def BindFinished (execution : Execution α) (continuation : α → Execution β)
    (state : (execution.bind continuation).State) (outcome : Except ExceptionObject β) : Prop :=
  match state with
  | .inl state =>
      (∃ exception, outcome = .error exception ∧ Finishes execution.step state (.error exception)) ∨
      ∃ value, Finishes execution.step state (.ok value) ∧
        Finishes (continuation value).step (continuation value).initial outcome
  | .inr ⟨value, state⟩ => Finishes (continuation value).step state outcome

private theorem bind_finished {execution : Execution α} {continuation : α → Execution β}
    {state : (execution.bind continuation).State} {outcome : Except ExceptionObject β}
    (h : Finishes (execution.bind continuation).step state outcome) :
    BindFinished execution continuation state outcome := by
  induction h with
  | @done state outcome h =>
    cases state with
    | inl state =>
      cases step_eq : execution.step state with
      | next following => simp [bind, step_eq] at h
      | unsupported => simp [bind, step_eq] at h
      | done result =>
        cases result with
        | ok value => simp [bind, step_eq] at h
        | error exception =>
          simp only [bind, step_eq, Step.done.injEq] at h
          exact Or.inl ⟨exception, h.symm, .done step_eq⟩
    | inr state =>
      obtain ⟨value, state⟩ := state
      cases step_eq : (continuation value).step state with
      | next following => simp [bind, step_eq] at h
      | unsupported => simp [bind, step_eq] at h
      | done result =>
        simp only [bind, step_eq, Step.done.injEq] at h
        exact .done (h ▸ step_eq)
  | @next state following outcome h _ ih =>
    cases state with
    | inl state =>
      cases step_eq : execution.step state with
      | next next =>
        simp only [bind, step_eq, Step.next.injEq] at h
        subst following
        rcases ih with ⟨exception, eq, rest⟩ | ⟨value, rest, final⟩
        · exact Or.inl ⟨exception, eq, .next step_eq rest⟩
        · exact Or.inr ⟨value, .next step_eq rest, final⟩
      | unsupported => simp [bind, step_eq] at h
      | done result =>
        cases result with
        | error exception => simp [bind, step_eq] at h
        | ok value =>
          simp only [bind, step_eq, Step.next.injEq] at h
          subst following
          exact Or.inr ⟨value, .done step_eq, ih⟩
    | inr state =>
      obtain ⟨value, state⟩ := state
      cases step_eq : (continuation value).step state with
      | done result => simp [bind, step_eq] at h
      | unsupported => simp [bind, step_eq] at h
      | next next =>
        simp only [bind, step_eq, Step.next.injEq] at h
        subst following
        exact .next step_eq ih

theorem halts_of_bind {execution : Execution α} {continuation : α → Execution β}
    (h : (execution.bind continuation).Halts) : execution.Halts := by
  obtain ⟨outcome, h⟩ := h
  rcases bind_finished h with ⟨exception, _, finished⟩ | ⟨value, finished, _⟩
  · exact ⟨.error exception, finished⟩
  · exact ⟨.ok value, finished⟩

theorem halts_continuation_of_bind {execution : Execution α} {continuation : α → Execution β}
    (finished : Finishes execution.step execution.initial (.ok value))
    (h : (execution.bind continuation).Halts) : (continuation value).Halts := by
  obtain ⟨outcome, h⟩ := h
  rcases bind_finished h with ⟨exception, _, thrown⟩ | ⟨result, returned, rest⟩
  · have := finished.unique thrown
    contradiction
  · have eq := finished.unique returned
    cases eq
    exact ⟨outcome, rest⟩

deriving instance DecidableEq for Except

/-- Finite observations distinguish unfinished execution from unsupported code. -/
inductive Observation (α : Type) where
  | pending
  | unsupported
  | done (outcome : Except ExceptionObject α)
deriving Repr, DecidableEq

def observeFrom (step : σ → Step σ α) : Nat → σ → Observation α
  | 0, _ => .pending
  | fuel + 1, state =>
      match step state with
      | .next following => observeFrom step fuel following
      | .done outcome => .done outcome
      | .unsupported => .unsupported

def observe (execution : Execution α) (fuel : Nat) : Observation α :=
  observeFrom execution.step fuel execution.initial

theorem finishes_of_observeFrom {step : σ → Step σ α} {state : σ}
    (h : observeFrom step fuel state = .done outcome) : Finishes step state outcome := by
  induction fuel generalizing state with
  | zero => simp [observeFrom] at h
  | succ fuel ih =>
      cases next : step state with
      | next following =>
          exact .next next (ih (by simpa [observeFrom, next] using h))
      | done result =>
          simp only [observeFrom, next, Observation.done.injEq] at h
          subst result
          exact .done next
      | unsupported => simp [observeFrom, next] at h

theorem finishes_of_observe {execution : Execution α}
    (h : execution.observe fuel = .done outcome) :
    Finishes execution.step execution.initial outcome := finishes_of_observeFrom h

/-- Observational equivalence includes both normal and exceptional termination. -/
def Equiv (left right : Execution α) : Prop :=
  ∀ outcome, Finishes left.step left.initial outcome ↔ Finishes right.step right.initial outcome

theorem Equiv.returns_iff {left right : Execution α} (h : left.Equiv right) :
    left.Returns ↔ right.Returns := by
  constructor <;> rintro ⟨value, finished⟩
  · exact ⟨value, (h _).mp finished⟩
  · exact ⟨value, (h _).mpr finished⟩

theorem Equiv.halts_iff {left right : Execution α} (h : left.Equiv right) :
    left.Halts ↔ right.Halts := by
  constructor <;> rintro ⟨outcome, finished⟩
  · exact ⟨outcome, (h _).mp finished⟩
  · exact ⟨outcome, (h _).mpr finished⟩

end Execution
end CleanXY.PyAst
