import lang.py.FormalSW.MachineSortAcquisition
import lang.py.FormalSW.MachineComparisonInvariant

/-! Extremum selection preserves original items for every primitive key-comparison outcome. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem extremum_choose_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout logical physical rename) (cursor : SequenceExtremum) (candidate score : Value)
    (best : Option (Value × Value)) (scoreInside : score.edge.Within logical.length)
    (bestInside : ∀ pair, best = some pair → PairWithin logical.length pair) :
    (relocateExtremum rename cursor).choose (relocateValue rename candidate) (relocateValue rename score)
        (best.map (relocatePair rename)) physical =
      (cursor.choose candidate score best logical).map
        (fun pair => (pair.1.map (relocatePair rename), physical)) := by
  cases best with
  | none => rfl
  | some pair =>
    rcases pair with ⟨winner, previous⟩
    have previousInside := (bestInside (winner, previous) rfl).2
    obtain ⟨result, read⟩ := compare_readonly logical (if cursor.maximum then .gt else .lt)
      score previous scoreInside previousInside
    have paired := layout.runtime.compare_complete layout.closed (if cursor.maximum then .gt else .lt)
      score previous scoreInside previousInside
    rw [read] at paired
    dsimp only [relocateExtremum]
    simp only [SequenceExtremum.choose, Option.map_some, relocatePair, Mutable.eval_bind]
    rw [paired, read]
    cases result with
    | none => simp [comparisonEval]
    | some result =>
      cases result with
      | error exception => simp [comparisonEval, Except.map]
      | ok better =>
        cases better <;> simp [comparisonEval, Except.map,
          relocateValue, Mutable.truth, scalarTruth, relocatePair]

theorem extremum_choose_effect (heap after : Mutable.Heap) (cursor : SequenceExtremum) (candidate score : Value)
    (best : Option (Value × Value)) (candidateInside : candidate.edge.Within heap.length)
    (scoreInside : score.edge.Within heap.length) (bestInside : ∀ pair, best = some pair → PairWithin heap.length pair)
    (outcome : Except ExceptionObject (Value × Value))
    (executed : cursor.choose candidate score best heap = some (outcome, after)) :
    after = heap ∧ ∀ pair, outcome = .ok pair → PairWithin heap.length pair := by
  cases best with
  | none =>
    simp [SequenceExtremum.choose] at executed
    rcases executed with ⟨rfl, rfl⟩
    exact ⟨rfl, by intro pair equal; cases equal; exact ⟨candidateInside, scoreInside⟩⟩
  | some pair =>
    rcases pair with ⟨winner, previous⟩
    have bounded := bestInside (winner, previous) rfl
    obtain ⟨result, read⟩ := compare_readonly heap (if cursor.maximum then .gt else .lt)
      score previous scoreInside bounded.2
    cases result with
    | none => simp [SequenceExtremum.choose, Mutable.eval_bind, read, comparisonEval] at executed
    | some result =>
      cases result with
      | error exception =>
        simp [SequenceExtremum.choose, Mutable.eval_bind, read, comparisonEval, Except.map] at executed
        rcases executed with ⟨rfl, rfl⟩
        exact ⟨rfl, by intros; contradiction⟩
      | ok better =>
        cases better <;>
          simp [SequenceExtremum.choose, Mutable.eval_bind, read, comparisonEval, Except.map,
            Mutable.truth, scalarTruth] at executed
        all_goals
          rcases executed with ⟨rfl, rfl⟩
          refine ⟨rfl, ?_⟩
          intro pair equal
          cases equal
          first | exact bounded | exact ⟨candidateInside, scoreInside⟩

theorem step_extremumKey_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value candidate : Value) (cursor : SequenceExtremum) (position : Nat)
    (best : Option (Value × Value)) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .extremumKey cursor position candidate best :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .extremumKey cursor position candidate best :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .extremumKey cursor position candidate best :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have captured := inside.2 (.extremumKey cursor position candidate best) (by simp)
  simp only [FrameWithin] at captured
  have raw := run_readonly_preserves logical physical rename logicalAnchors physicalAnchors
    (cursor.choose candidate value best)
    ((relocateExtremum rename cursor).choose (relocateValue rename candidate) (relocateValue rename value)
      (best.map (relocatePair rename))) (relocatePair rename)
    (fun updated heap => .next ⟨.extremumLoop cursor (position + 1) (some updated), stack, heap⟩)
    (fun updated heap => .next ⟨.extremumLoop (relocateExtremum rename cursor) (position + 1) (some updated),
      stack.map (relocateFrame rename), heap⟩)
    globals layout globalsInside
    (fun outcome after executed => (extremum_choose_effect logical after cursor candidate value best captured.1 inside.1
      captured.2.2 outcome executed).1)
    (extremum_choose_relocates logical physical rename layout cursor candidate value best inside.1 captured.2.2) (by
      intro updated executed
      have bounded := (extremum_choose_effect logical logical cursor candidate value best captured.1 inside.1
        captured.2.2 _ executed).2 updated rfl
      apply Preserves.unchanged layout
      · rfl
      · exact ⟨⟨captured.2.1, by intro pair equal; cases equal; exact bounded⟩,
          fun frame member => inside.2 frame (List.mem_cons_of_mem _ member)⟩
      · rfl)
  simpa only [step, relocateState, relocateWork, List.map_cons, relocateFrame] using
    raw.protectGenerator (.extremumKey cursor position candidate best :: stack) inside.2

end FormalSW.PyAst.HeapCalls.Relocation
