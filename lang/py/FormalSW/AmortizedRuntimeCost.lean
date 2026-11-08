import lang.py.FormalSW.RuntimeCost

/-! Potential accounting over the same charged execution. No operation loses its
actual tariff: each derived bound includes the potential left in the final state.
Composition cancels intermediate credits, so fresh allocations and mutations can
be combined without assuming constant worst-case append time. -/
namespace FormalSW.PyAst.RuntimeCost.Amortized

def Reaches (step : σ → Step σ α) (charge : σ → Option Nat) (potential : σ → Nat)
    (initial : σ) (budget : Nat) (final : σ) : Prop :=
  ∃ cost, RuntimeCost.Reaches step charge initial cost final ∧
    cost + potential final ≤ budget + potential initial

namespace Reaches

theorem refl : Reaches step charge potential state 0 state := ⟨0, .refl, by omega⟩

theorem mono (run : Reaches step charge potential initial small final) (larger : small ≤ large) :
    Reaches step charge potential initial large final := by
  obtain ⟨cost, trace, paid⟩ := run
  exact ⟨cost, trace, by omega⟩

theorem next (transition : step initial = .next following) (measured : charge initial = some amount)
    (paid : amount + potential following ≤ budget + potential initial) :
    Reaches step charge potential initial budget following :=
  ⟨amount, by simpa using RuntimeCost.Reaches.next transition measured .refl, paid⟩

theorem trans (first : Reaches step charge potential a ca b)
    (second : Reaches step charge potential b cb c) :
    Reaches step charge potential a (ca + cb) c := by
  obtain ⟨actualA, traceA, paidA⟩ := first
  obtain ⟨actualB, traceB, paidB⟩ := second
  exact ⟨actualA + actualB, traceA.trans traceB, by omega⟩

/-- Final execution also has to pay its terminal state; retained credits are discarded. -/
theorem finishes (run : Reaches step charge potential initial budget final)
    (rest : RuntimeCost.Finishes step charge final terminal outcome) :
    ∃ cost, RuntimeCost.Finishes step charge initial cost outcome ∧
      cost ≤ budget + potential initial + terminal := by
  obtain ⟨cost, trace, paid⟩ := run
  exact ⟨cost + terminal, trace.finishes rest, by omega⟩

end Reaches
end FormalSW.PyAst.RuntimeCost.Amortized
