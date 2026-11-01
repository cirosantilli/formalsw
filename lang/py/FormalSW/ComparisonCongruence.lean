import lang.py.FormalSW.ComparisonEquality

/-! Equality substitution preserves the whole partial result, including unsupported cases. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

theorem lex_equality_symmetric (equal less : Value → Value → HeapSort.Result Bool)
    (symmetric : ∀ left right, equal left right = equal right left) (xs ys : List Value) :
    HeapSort.lex equal less true xs ys = HeapSort.lex equal less true ys xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp only [HeapSort.lex, ← symmetric x y]
      cases equal x y with
      | none => rfl
      | some outcome =>
        cases outcome with
        | error exception => rfl
        | ok flag => cases flag <;> simp only [ih, if_true]

/-- Unlike the true-result symmetry rule, this also relates false and unsupported outcomes. -/
theorem compare_equality_symmetric (heap : Heap) (fuel : Nat) (left right : Value) :
    HeapSort.compare fuel heap true left right = HeapSort.compare fuel heap true right left := by
  induction fuel generalizing left right with
  | zero => rfl
  | succ fuel ih =>
    cases left with
    | scalar left =>
      cases right with
      | scalar right => simp [HeapSort.compare, scalarCompare_equal, eq_comm]
      | ref right =>
        cases found : heap[right]? with
        | none => simp [HeapSort.compare, found]
        | some object => cases object <;> simp [HeapSort.compare, found]
    | ref left =>
      cases right with
      | scalar right =>
        cases found : heap[left]? with
        | none => simp [HeapSort.compare, found]
        | some object => cases object <;> simp [HeapSort.compare, found]
      | ref right =>
        have symmetric := lex_equality_symmetric (HeapSort.compare fuel heap true)
          (HeapSort.compare fuel heap false) ih
        have references : (left == right) = (right == left) := by
          apply Bool.eq_iff_iff.mpr
          simp only [beq_iff_eq]
          exact eq_comm
        have sequences (xs ys : List Value) :
            (if left == right then some (.ok true)
             else if xs.length != ys.length then some (.ok false)
             else HeapSort.lex (HeapSort.compare fuel heap true) (HeapSort.compare fuel heap false) true xs ys) =
            (if right == left then some (.ok true)
             else if ys.length != xs.length then some (.ok false)
             else HeapSort.lex (HeapSort.compare fuel heap true) (HeapSort.compare fuel heap false) true ys xs) := by
          have lengths : (xs.length != ys.length) = (ys.length != xs.length) := by
            apply Bool.eq_iff_iff.mpr
            simp only [bne_iff_ne]
            exact ne_comm
          rw [references, lengths, symmetric xs ys]
        cases first : heap[left]? with
        | none =>
          cases second : heap[right]? with
          | none => simp [HeapSort.compare, first, second]
          | some object => cases object <;> simp [HeapSort.compare, first, second]
        | some object =>
          cases second : heap[right]? with
          | none => cases object <;> simp [HeapSort.compare, first, second]
          | some otherObject =>
            cases object <;> cases otherObject <;>
              simp only [HeapSort.compare, first, second, Bool.true_and]
            all_goals first | exact sequences _ _ | rw [references] | rfl

theorem lex_equality_substitute (equal less : Value → Value → HeapSort.Result Bool)
    (relation : Value → Value → Prop)
    (substitute : ∀ left replacement right, relation left replacement → equal left right = equal replacement right)
    (xs replacements ys : List Value) (related : RelatedItems relation xs replacements) :
    HeapSort.lex equal less true xs ys = HeapSort.lex equal less true replacements ys := by
  induction xs generalizing replacements ys with
  | nil => cases replacements <;> cases ys <;> simp_all [RelatedItems, HeapSort.lex]
  | cons x xs ih =>
    cases replacements with
    | nil => cases related
    | cons replacement replacements =>
      cases ys with
      | nil => rfl
      | cons y ys =>
        simp only [HeapSort.lex, substitute x replacement y related.1]
        cases equal replacement y with
        | none => rfl
        | some outcome =>
          cases outcome with
          | error exception => rfl
          | ok flag => cases flag <;> simp only [ih replacements ys related.2, if_true]

/-- Replacing an equal operand retains even unresolved comparisons at the same depth. -/
theorem compare_equality_substitute (heap : Heap) (fuel : Nat) (left replacement right : Value)
    (related : EqualAt fuel heap left replacement) :
    HeapSort.compare fuel heap true left right = HeapSort.compare fuel heap true replacement right := by
  induction fuel generalizing left replacement right with
  | zero => cases related
  | succ fuel ih =>
    cases left with
    | scalar left =>
      cases replacement with
      | ref replacement => cases related
      | scalar replacement =>
        cases right with
        | scalar right =>
          change equalityScalar left = equalityScalar replacement at related
          simp [HeapSort.compare, scalarCompare_equal, related]
        | ref right =>
          cases found : heap[right]? with
          | none => simp [HeapSort.compare, found]
          | some object => cases object <;> simp [HeapSort.compare, found]
    | ref left =>
      cases replacement with
      | scalar replacement => cases related
      | ref replacement =>
        rcases related with ⟨same, _⟩ | ⟨isTuple, xs, replacements, leftFound, replacementFound, items⟩
        · subst replacement
          rfl
        · have equal : HeapSort.compare (fuel + 1) heap true (.ref left) (.ref replacement) = some (.ok true) :=
            (compare_equal_true_iff _ _ _ _).mpr
              (Or.inr ⟨isTuple, xs, replacements, leftFound, replacementFound, items⟩)
          have lengths := items.length_eq
          have sequences (ys : List Value) := lex_equality_substitute
            (HeapSort.compare fuel heap true) (HeapSort.compare fuel heap false) (EqualAt fuel heap) ih
            xs replacements ys items
          cases right with
          | scalar right =>
            cases isTuple <;> simp [comparisonObject] at leftFound replacementFound <;>
              simp [HeapSort.compare, leftFound, replacementFound]
          | ref right =>
            by_cases sameLeft : left = right
            · subst right
              rw [compare_equal_reflexive heap fuel (.ref left) (List.getElem?_eq_some_iff.mp leftFound).1]
              exact (compare_equal_symmetric heap (fuel + 1) (.ref left) (.ref replacement) equal).symm
            · by_cases sameReplacement : replacement = right
              · subst right
                rw [compare_equal_reflexive heap fuel (.ref replacement) (List.getElem?_eq_some_iff.mp replacementFound).1]
                exact equal
              · cases found : heap[right]? with
                | none =>
                  cases isTuple <;> simp [comparisonObject] at leftFound replacementFound <;>
                    simp [HeapSort.compare, leftFound, replacementFound, found]
                | some object =>
                  cases isTuple <;> simp [comparisonObject] at leftFound replacementFound <;> cases object <;>
                    simp [HeapSort.compare, leftFound, replacementFound, found, sameLeft, sameReplacement, lengths, sequences]

theorem compare_equality_substitute_right (heap : Heap) (fuel : Nat) (left right replacement : Value)
    (related : EqualAt fuel heap right replacement) :
    HeapSort.compare fuel heap true left right = HeapSort.compare fuel heap true left replacement := by
  rw [compare_equality_symmetric heap fuel left right, compare_equality_symmetric heap fuel left replacement]
  exact compare_equality_substitute heap fuel right replacement left related

/-- Native equality classes are congruence classes for every full partial equality result. -/
theorem compare_equality_native_substitute (heap : Heap) (left replacement right : Value)
    (equal : HeapSort.compare (HeapSort.comparisonFuel heap) heap true left replacement = some (.ok true)) :
    HeapSort.compare (HeapSort.comparisonFuel heap) heap true left right =
      HeapSort.compare (HeapSort.comparisonFuel heap) heap true replacement right :=
  compare_equality_substitute heap (HeapSort.comparisonFuel heap) left replacement right
    ((compare_equal_true_iff _ _ _ _).mp equal)

end FormalSW.PyAst.Mutable.Relocation
