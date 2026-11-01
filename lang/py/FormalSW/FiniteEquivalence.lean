import lang.py.FormalSW.KeyRelocation

/-! Increasing equivalence relations stabilize by merging finitely many classes. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

structure EquivalenceBelow (limit : Nat) (related : Nat → Nat → Prop) : Prop where
  reflexive : ∀ index < limit, related index index
  symmetric : ∀ left < limit, ∀ right < limit, related left right → related right left
  transitive : ∀ left < limit, ∀ middle < limit, ∀ right < limit,
    related left middle → related middle right → related left right

/-- Every class has a least representative, without requiring a decidable relation. -/
theorem EquivalenceBelow.representative {limit : Nat} {related : Nat → Nat → Prop}
    (equivalent : EquivalenceBelow limit related) (index : Nat) (inside : index < limit) :
    ∃ representative, representative < limit ∧ representative ≤ index ∧ related index representative ∧
      ∀ smaller < representative, ¬related representative smaller := by
  classical
  induction index using Nat.strongRecOn with
  | ind index ih =>
    by_cases earlier : ∃ smaller, smaller < index ∧ related index smaller
    · obtain ⟨smaller, smallerThan, relatedSmaller⟩ := earlier
      obtain ⟨representative, bounded, before, relatedRepresentative, least⟩ :=
        ih smaller smallerThan (by omega)
      exact ⟨representative, bounded, by omega,
        equivalent.transitive index inside smaller (by omega) representative bounded relatedSmaller relatedRepresentative,
        least⟩
    · exact ⟨index, inside, Nat.le_refl _, equivalent.reflexive index inside,
        fun smaller smallerThan relatedSmaller => earlier ⟨smaller, smallerThan, relatedSmaller⟩⟩

/-- A strict extension must remove a least representative by merging two classes. -/
theorem EquivalenceBelow.eq_of_preserved_representatives {limit : Nat} {first second : Nat → Nat → Prop}
    (firstEquiv : EquivalenceBelow limit first) (secondEquiv : EquivalenceBelow limit second)
    (extension : ∀ left < limit, ∀ right < limit, first left right → second left right)
    (preserved : ∀ index < limit, (∀ smaller < index, ¬first index smaller) →
      ∀ smaller < index, ¬second index smaller)
    (left right : Nat) (leftInside : left < limit) (rightInside : right < limit) :
    second left right ↔ first left right := by
  constructor
  · intro related
    obtain ⟨a, aInside, _, leftRepresentative, aLeast⟩ := firstEquiv.representative left leftInside
    obtain ⟨b, bInside, _, rightRepresentative, bLeast⟩ := firstEquiv.representative right rightInside
    have ab : second a b :=
      secondEquiv.transitive a aInside left leftInside b bInside
        (secondEquiv.symmetric left leftInside a aInside (extension _ leftInside _ aInside leftRepresentative))
        (secondEquiv.transitive left leftInside right rightInside b bInside related
          (extension _ rightInside _ bInside rightRepresentative))
    have same : a = b := by
      by_cases smaller : a < b
      · exact False.elim (preserved b bInside bLeast a smaller (secondEquiv.symmetric a aInside b bInside ab))
      · by_cases larger : b < a
        · exact False.elim (preserved a aInside aLeast b larger ab)
        · omega
    subst b
    exact firstEquiv.transitive left leftInside a aInside right rightInside leftRepresentative
      (firstEquiv.symmetric right rightInside a aInside rightRepresentative)
  · exact extension left leftInside right rightInside

/-- Each strict extension removes a class representative, so there are at most `limit` such steps.
The step hypothesis forbids restarting after a stationary iteration. -/
theorem finite_equivalence_stable (limit : Nat) (related : Nat → Nat → Nat → Prop)
    (equivalent : ∀ fuel, EquivalenceBelow limit (related fuel))
    (extension : ∀ fuel left, left < limit → ∀ right, right < limit →
      related fuel left right → related (fuel + 1) left right)
    (step : ∀ fuel, (∀ left < limit, ∀ right < limit, related (fuel + 1) left right ↔ related fuel left right) →
      ∀ left < limit, ∀ right < limit, related (fuel + 2) left right ↔ related (fuel + 1) left right) :
    ∀ left < limit, ∀ right < limit, related (limit + 1) left right ↔ related limit left right := by
  classical
  let resolve : Nat → Nat → Option Unit := fun fuel index =>
    if ∃ smaller, smaller < index ∧ related fuel index smaller then some () else none
  have recover (fuel : Nat) (same : ∀ index < limit, resolve (fuel + 1) index = resolve fuel index) :
      ∀ left < limit, ∀ right < limit, related (fuel + 1) left right ↔ related fuel left right := by
    intro left leftInside right rightInside
    apply (equivalent fuel).eq_of_preserved_representatives (equivalent (fuel + 1))
      (extension fuel) ?_ left right leftInside rightInside
    intro index inside least smaller smallerThan relatedSmaller
    have old : ¬ ∃ earlier, earlier < index ∧ related fuel index earlier := by
      rintro ⟨earlier, before, matched⟩
      exact least earlier before matched
    have new : ∃ earlier, earlier < index ∧ related (fuel + 1) index earlier :=
      ⟨smaller, smallerThan, relatedSmaller⟩
    have impossible := same index inside
    simp [resolve, old, new] at impossible
  have stable := finite_resolution_stable limit resolve
    (by
      intro fuel index inside outcome resolved
      have monotone : (∃ smaller, smaller < index ∧ related fuel index smaller) →
          ∃ smaller, smaller < index ∧ related (fuel + 1) index smaller := by
        rintro ⟨smaller, before, matched⟩
        exact ⟨smaller, before, extension fuel index inside smaller (by omega) matched⟩
      simp only [resolve] at resolved ⊢
      split at resolved
      · rename_i earlier
        simp [monotone earlier] at resolved ⊢
      · cases resolved)
    (by
      intro fuel same index inside
      have next := step fuel (recover fuel same)
      have earlier : (∃ smaller, smaller < index ∧ related (fuel + 2) index smaller) ↔
          ∃ smaller, smaller < index ∧ related (fuel + 1) index smaller := by
        constructor
        · rintro ⟨smaller, before, matched⟩
          exact ⟨smaller, before, (next index inside smaller (by omega)).mp matched⟩
        · rintro ⟨smaller, before, matched⟩
          exact ⟨smaller, before, (next index inside smaller (by omega)).mpr matched⟩
      simp only [resolve, earlier])
  exact recover limit stable

end FormalSW.PyAst.Mutable.Relocation
