import lang.py.FormalSW.Choices
import lang.py.FormalSW.MutableSimulation

/-! Match possible runs without requiring every pair of schedules to agree. -/
namespace FormalSW.PyAst.Mutable
set_option Elab.async false

/-- Observable completions, interpreter errors, support and divergence all agree. -/
structure Call.BehaviorEquiv (left right : Call) : Prop where
  completed : left.Equiv right
  outerErrors : ∀ error,
    PyAst.Finishes left.execution.step left.execution.initial (.error error) ↔
      PyAst.Finishes right.execution.step right.execution.initial (.error error)
  supported : left.execution.Supported ↔ right.execution.Supported
  diverges : left.Diverges ↔ right.Diverges

theorem Call.BehaviorEquiv.refl (call : Call) : call.BehaviorEquiv call :=
  ⟨⟨fun result finished => ⟨result, finished, Or.inl rfl⟩,
    fun result finished => ⟨result, finished, Or.inl rfl⟩⟩, fun _ => Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem Call.BehaviorEquiv.of_finishes {left right : Call} {first second : Completion}
    (leftRun : left.Finishes first) (rightRun : right.Finishes second)
    (same : first.Equivalent second) : left.BehaviorEquiv right := by
  refine ⟨Call.equiv_of_finishes leftRun rightRun same, ?_,
    ⟨fun _ => Execution.supported_of_finishes rightRun, fun _ => Execution.supported_of_finishes leftRun⟩, ?_⟩
  · intro error
    constructor
    · intro impossible
      cases impossible.unique leftRun
    · intro impossible
      cases impossible.unique rightRun
  · exact ⟨fun divergent => False.elim (Call.diverges_not_halts divergent ⟨first, leftRun⟩),
      fun divergent => False.elim (Call.diverges_not_halts divergent ⟨second, rightRun⟩)⟩

theorem Call.BehaviorEquiv.of_diverges {left right : Call}
    (leftRun : left.Diverges) (rightRun : right.Diverges) : left.BehaviorEquiv right := by
  refine ⟨⟨?_, ?_⟩, ?_, ⟨fun _ => rightRun.supported, fun _ => leftRun.supported⟩,
    ⟨fun _ => rightRun, fun _ => leftRun⟩⟩
  · intro result finished
    exact False.elim (Call.diverges_not_halts leftRun ⟨result, finished⟩)
  · intro result finished
    exact False.elim (Call.diverges_not_halts rightRun ⟨result, finished⟩)
  · intro error
    constructor
    · intro finished
      exact False.elim (Execution.diverges_not_halts leftRun ⟨_, finished⟩)
    · intro finished
      exact False.elim (Execution.diverges_not_halts rightRun ⟨_, finished⟩)

theorem Call.BehaviorEquiv.of_bisimulation {left right : Call}
    {states : left.execution.State → right.execution.State → Prop}
    {outcomes : Except ExceptionObject Completion → Except ExceptionObject Completion → Prop}
    (paired : Execution.Bisimulation left.execution right.execution states outcomes)
    (observable : ∀ a b, outcomes a b → Call.EquivalentOutcomes a b) : left.BehaviorEquiv right := by
  refine ⟨Call.equiv_of_bisimulation paired observable, ?_, paired.supported_iff, paired.diverges_iff⟩
  intro error
  constructor
  · intro finished
    obtain ⟨other, related, transported⟩ := paired.finishes finished
    have same := observable _ _ related
    cases other with
    | ok completion => exact False.elim same
    | error exception => exact same ▸ transported
  · intro finished
    obtain ⟨other, related, transported⟩ := paired.flip.finishes finished
    have same := observable _ _ related
    cases other with
    | ok completion => exact False.elim same
    | error exception => exact same ▸ transported

/-- Every permitted run has a matching run on the other side, in both directions.
Schedules may differ and need not be paired by a fixed bijection. -/
def CallFamily.PossibleEquiv (left right : CallFamily) : Prop :=
  (∀ choices, ∃ other, (left.run choices).BehaviorEquiv (right.run other)) ∧
  (∀ choices, ∃ other, (left.run other).BehaviorEquiv (right.run choices))

theorem CallFamily.PossibleEquiv.refl (family : CallFamily) : family.PossibleEquiv family :=
  ⟨fun choices => ⟨choices, Call.BehaviorEquiv.refl _⟩, fun choices => ⟨choices, Call.BehaviorEquiv.refl _⟩⟩

theorem CallFamily.PossibleEquiv.of_pointwise {left right : CallFamily}
    (paired : ∀ choices, (left.run choices).BehaviorEquiv (right.run choices)) : left.PossibleEquiv right :=
  ⟨fun choices => ⟨choices, paired choices⟩, fun choices => ⟨choices, paired choices⟩⟩

/-- Reindexing choices may account for different numbers or positions of internal choices. -/
theorem CallFamily.PossibleEquiv.of_reindex {left right : CallFamily}
    (reindex : ChoiceSchedule → ChoiceSchedule) (onto : Function.Surjective reindex)
    (paired : ∀ choices, (left.run choices).BehaviorEquiv (right.run (reindex choices))) : left.PossibleEquiv right := by
  refine ⟨fun choices => ⟨reindex choices, paired choices⟩, ?_⟩
  intro choices
  obtain ⟨other, rfl⟩ := onto choices
  exact ⟨other, paired other⟩

theorem CallFamily.PossibleEquiv.supported_iff {left right : CallFamily} (paired : left.PossibleEquiv right) :
    left.Supported ↔ right.Supported := by
  constructor
  · intro supported choices
    obtain ⟨other, same⟩ := paired.2 choices
    exact same.supported.mp (supported other)
  · intro supported choices
    obtain ⟨other, same⟩ := paired.1 choices
    exact same.supported.mpr (supported other)

theorem CallFamily.PossibleEquiv.possible_diverges_iff {left right : CallFamily} (paired : left.PossibleEquiv right) :
    (∃ choices, (left.run choices).Diverges) ↔ ∃ choices, (right.run choices).Diverges := by
  constructor
  · rintro ⟨choices, divergent⟩
    obtain ⟨other, same⟩ := paired.1 choices
    exact ⟨other, same.diverges.mp divergent⟩
  · rintro ⟨choices, divergent⟩
    obtain ⟨other, same⟩ := paired.2 choices
    exact ⟨other, same.diverges.mpr divergent⟩

theorem CallFamily.PossibleEquiv.possible_halts_iff {left right : CallFamily} (paired : left.PossibleEquiv right) :
    (∃ choices, (left.run choices).Halts) ↔ ∃ choices, (right.run choices).Halts := by
  constructor
  · rintro ⟨choices, finished⟩
    obtain ⟨other, same⟩ := paired.1 choices
    exact ⟨other, same.completed.halts_iff.mp finished⟩
  · rintro ⟨choices, finished⟩
    obtain ⟨other, same⟩ := paired.2 choices
    exact ⟨other, same.completed.halts_iff.mpr finished⟩

end FormalSW.PyAst.Mutable
