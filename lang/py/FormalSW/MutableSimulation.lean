import lang.py.FormalSW.ExecutionSimulation
import lang.py.FormalSW.MutableGlobals

/-! Connect execution relations to the existing observable mutable-call contract. -/
namespace FormalSW.PyAst.Mutable.Call
set_option Elab.async false

/-- Completed calls retain the graph-based contract; interpreter exceptions must match exactly. -/
def EquivalentOutcomes : Except ExceptionObject Completion → Except ExceptionObject Completion → Prop
  | .ok left, .ok right => left.Equivalent right
  | .error left, .error right => left = right
  | _, _ => False

theorem equiv_of_bisimulation {left right : Call}
    {states : left.execution.State → right.execution.State → Prop}
    {outcomes : Except ExceptionObject Completion → Except ExceptionObject Completion → Prop}
    (paired : Execution.Bisimulation left.execution right.execution states outcomes)
    (observable : ∀ a b, outcomes a b → EquivalentOutcomes a b) : left.Equiv right := by
  constructor
  · intro result finished
    obtain ⟨other, related, transported⟩ := paired.finishes finished
    have same := observable _ _ related
    cases other with
    | error exception => exact False.elim same
    | ok completion => exact ⟨completion, transported, same⟩
  · intro result finished
    obtain ⟨other, related, transported⟩ := paired.flip.finishes finished
    have same := observable _ _ related
    cases other with
    | error exception => exact False.elim same
    | ok completion => exact ⟨completion, transported, same⟩

/-- The public equivalence contract can be established together with the stronger
support and divergence guarantees, rather than inferring divergence from nontermination. -/
theorem behavior_of_bisimulation {left right : Call}
    {states : left.execution.State → right.execution.State → Prop}
    {outcomes : Except ExceptionObject Completion → Except ExceptionObject Completion → Prop}
    (paired : Execution.Bisimulation left.execution right.execution states outcomes)
    (observable : ∀ a b, outcomes a b → EquivalentOutcomes a b) :
    left.Equiv right ∧ (left.execution.Supported ↔ right.execution.Supported) ∧
      (left.Diverges ↔ right.Diverges) :=
  ⟨equiv_of_bisimulation paired observable, paired.supported_iff, paired.diverges_iff⟩

end FormalSW.PyAst.Mutable.Call
