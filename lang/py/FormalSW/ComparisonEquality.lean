import lang.py.FormalSW.ComparisonStability
import lang.py.FormalSW.FiniteEquivalence

/-! Structural laws for successful equality at each recursion depth. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

/-- Boolean and integer representatives share Python's numeric equality classes. -/
def equalityScalar : Constant → Constant
  | .bool value => .int (if value then 1 else 0)
  | value => value

theorem scalarCompare_equal (left right : Constant) :
    scalarCompare .eq left right = some (decide (equalityScalar left = equalityScalar right)) := by
  cases left <;> cases right <;> simp [scalarCompare, equalityScalar, evalCmpOp]

/-- Relate corresponding elements, requiring the lists to have equal lengths. -/
def RelatedItems (relation : Value → Value → Prop) : List Value → List Value → Prop
  | [], [] => True
  | left :: lefts, right :: rights => relation left right ∧ RelatedItems relation lefts rights
  | _, _ => False

theorem RelatedItems.length_eq {relation : Value → Value → Prop} {left right : List Value}
    (related : RelatedItems relation left right) : left.length = right.length := by
  induction left generalizing right with
  | nil => cases right <;> simp_all [RelatedItems]
  | cons head tail ih =>
    cases right with
    | nil => cases related
    | cons head' tail' => exact congrArg Nat.succ (ih related.2)

theorem RelatedItems.symm {relation : Value → Value → Prop}
    (symmetric : ∀ left right, relation left right → relation right left)
    {left right : List Value} (related : RelatedItems relation left right) : RelatedItems relation right left := by
  induction left generalizing right with
  | nil => cases right <;> simp_all [RelatedItems]
  | cons head tail ih =>
    cases right with
    | nil => cases related
    | cons head' tail' => exact ⟨symmetric _ _ related.1, ih related.2⟩

theorem RelatedItems.trans {relation : Value → Value → Prop}
    (transitive : ∀ left middle right, relation left middle → relation middle right → relation left right)
    {left middle right : List Value} (first : RelatedItems relation left middle)
    (second : RelatedItems relation middle right) : RelatedItems relation left right := by
  induction left generalizing middle right with
  | nil => cases middle <;> cases right <;> simp_all [RelatedItems]
  | cons head tail ih =>
    cases middle with
    | nil => cases first
    | cons mid mids =>
      cases right with
      | nil => cases second
      | cons last lasts => exact ⟨transitive _ _ _ first.1 second.1, ih first.2 second.2⟩

theorem lex_equality_true_iff (equal less : Value → Value → HeapSort.Result Bool) (xs ys : List Value) :
    HeapSort.lex equal less true xs ys = some (.ok true) ↔
      RelatedItems (fun left right => equal left right = some (.ok true)) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [HeapSort.lex, RelatedItems]
  | cons x xs ih =>
    cases ys with
    | nil => simp [HeapSort.lex, RelatedItems]
    | cons y ys =>
      cases first : equal x y with
      | none => simp [HeapSort.lex, RelatedItems, first]
      | some outcome =>
        cases outcome with
        | error exception => simp [HeapSort.lex, RelatedItems, first]
        | ok flag => cases flag <;> simp [HeapSort.lex, RelatedItems, first, ih]

theorem guarded_lex_equality_true_iff (equal less : Value → Value → HeapSort.Result Bool) (xs ys : List Value) :
    (if xs.length = ys.length then HeapSort.lex equal less true xs ys else some (.ok false)) =
        some (.ok true) ↔ RelatedItems (fun left right => equal left right = some (.ok true)) xs ys := by
  by_cases lengths : xs.length = ys.length
  · simp [lengths, lex_equality_true_iff]
  · have unrelated : ¬ RelatedItems (fun left right => equal left right = some (.ok true)) xs ys :=
      fun related => lengths related.length_eq
    simp [lengths, unrelated]

/-- A proof-facing equality relation; identity can stop before inspecting recursive children. -/
def EqualAt : Nat → Heap → Value → Value → Prop
  | 0, _, _, _ => False
  | _ + 1, _, .scalar left, .scalar right => equalityScalar left = equalityScalar right
  | fuel + 1, heap, .ref left, .ref right =>
      (left = right ∧ (∃ object, heap[left]? = some object)) ∨
        ∃ isTuple xs ys, heap[left]? = some (comparisonObject isTuple xs) ∧
          heap[right]? = some (comparisonObject isTuple ys) ∧ RelatedItems (EqualAt fuel heap) xs ys
  | _ + 1, _, _, _ => False

theorem compare_equal_true_iff (fuel : Nat) (heap : Heap) (left right : Value) :
    HeapSort.compare fuel heap true left right = some (.ok true) ↔ EqualAt fuel heap left right := by
  induction fuel generalizing left right with
  | zero => simp [HeapSort.compare, EqualAt]
  | succ fuel ih =>
    cases left with
    | scalar left =>
      cases right with
      | scalar right => simp [HeapSort.compare, scalarCompare_equal, EqualAt]
      | ref right =>
        cases found : heap[right]? with
        | none => simp [HeapSort.compare, EqualAt, found]
        | some object => cases object <;> simp [HeapSort.compare, EqualAt, found]
    | ref left =>
      cases right with
      | scalar right =>
        cases found : heap[left]? with
        | none => simp [HeapSort.compare, EqualAt, found]
        | some object => cases object <;> simp [HeapSort.compare, EqualAt, found]
      | ref right =>
        by_cases same : left = right
        · subst right
          cases found : heap[left]? with
          | none => simp [HeapSort.compare, EqualAt, found]
          | some object => cases object <;> simp [HeapSort.compare, EqualAt, found]
        · have relation : (fun left right => HeapSort.compare fuel heap true left right = some (.ok true)) =
              EqualAt fuel heap := funext (fun left => funext (fun right => propext (ih left right)))
          cases first : heap[left]? with
          | none => simp [HeapSort.compare, EqualAt, first, same]
          | some object =>
            cases second : heap[right]? with
            | none =>
              cases object <;> simp [HeapSort.compare, EqualAt, first, second, same, comparisonObject]
            | some otherObject =>
              cases object <;> cases otherObject <;>
                simp [HeapSort.compare, EqualAt, first, second, same, Bool.exists_bool,
                  comparisonObject, guarded_lex_equality_true_iff, relation]

theorem EqualAt.symm (fuel : Nat) (heap : Heap) (left right : Value)
    (related : EqualAt fuel heap left right) : EqualAt fuel heap right left := by
  induction fuel generalizing left right with
  | zero => cases related
  | succ fuel ih =>
    cases left <;> cases right
    · exact Eq.symm related
    · cases related
    · cases related
    · rcases related with ⟨same, valid⟩ | ⟨isTuple, xs, ys, first, second, items⟩
      · subst same
        exact Or.inl ⟨rfl, valid⟩
      · exact Or.inr ⟨isTuple, ys, xs, second, first, items.symm ih⟩

theorem EqualAt.trans (fuel : Nat) (heap : Heap) (left middle right : Value)
    (first : EqualAt fuel heap left middle) (second : EqualAt fuel heap middle right) :
    EqualAt fuel heap left right := by
  induction fuel generalizing left middle right with
  | zero => cases first
  | succ fuel ih =>
    cases left <;> cases middle <;> cases right
    · exact Eq.trans first second
    · cases second
    · cases first
    · cases first
    · cases first
    · cases first
    · cases second
    · rcases first with ⟨same, valid⟩ | ⟨isTuple, xs, ys, leftFound, middleFound, xy⟩
      · subst same
        exact second
      · rcases second with ⟨same, valid⟩ | ⟨otherTuple, ys', zs, middleFound', rightFound, yz⟩
        · subst same
          exact Or.inr ⟨isTuple, xs, ys, leftFound, middleFound, xy⟩
        · have shapes := middleFound.symm.trans middleFound'
          cases isTuple <;> cases otherTuple <;> simp [comparisonObject] at shapes
          all_goals
            subst ys'
            exact Or.inr ⟨_, xs, zs, leftFound, rightFound, xy.trans ih yz⟩

theorem compare_equal_reflexive (heap : Heap) (fuel : Nat) (value : Value)
    (inside : value.edge.Within heap.length) :
    HeapSort.compare (fuel + 1) heap true value value = some (.ok true) := by
  apply (compare_equal_true_iff _ _ _ _).mpr
  cases value with
  | scalar value => rfl
  | ref address => exact Or.inl ⟨rfl, ⟨_, List.getElem?_eq_getElem inside⟩⟩

theorem compare_equal_symmetric (heap : Heap) (fuel : Nat) (left right : Value)
    (compared : HeapSort.compare fuel heap true left right = some (.ok true)) :
    HeapSort.compare fuel heap true right left = some (.ok true) :=
  (compare_equal_true_iff _ _ _ _).mpr (((compare_equal_true_iff _ _ _ _).mp compared).symm _ _ _ _)

theorem compare_equal_transitive (heap : Heap) (fuel : Nat) (left middle right : Value)
    (first : HeapSort.compare fuel heap true left middle = some (.ok true))
    (second : HeapSort.compare fuel heap true middle right = some (.ok true)) :
    HeapSort.compare fuel heap true left right = some (.ok true) :=
  (compare_equal_true_iff _ _ _ _).mpr
    (EqualAt.trans fuel heap left middle right ((compare_equal_true_iff _ _ _ _).mp first)
      ((compare_equal_true_iff _ _ _ _).mp second))

theorem EqualAt.refs_inside (fuel : Nat) (heap : Heap) (left right : Nat)
    (related : EqualAt fuel heap (.ref left) (.ref right)) : left < heap.length ∧ right < heap.length := by
  cases fuel with
  | zero => cases related
  | succ fuel =>
    rcases related with ⟨same, object, found⟩ | ⟨isTuple, xs, ys, first, second, items⟩
    · subst right
      exact ⟨(List.getElem?_eq_some_iff.mp found).1, (List.getElem?_eq_some_iff.mp found).1⟩
    · exact ⟨(List.getElem?_eq_some_iff.mp first).1, (List.getElem?_eq_some_iff.mp second).1⟩

theorem EqualAt.positive_congr (heap : Heap) (first second : Nat)
    (same : ∀ left < heap.length, ∀ right < heap.length,
      EqualAt (first + 1) heap (.ref left) (.ref right) ↔ EqualAt (second + 1) heap (.ref left) (.ref right))
    (left right : Value) : EqualAt (first + 1) heap left right ↔ EqualAt (second + 1) heap left right := by
  cases left with
  | scalar left => cases right <;> exact Iff.rfl
  | ref left =>
    cases right with
    | scalar right => exact Iff.rfl
    | ref right =>
      by_cases inside : left < heap.length ∧ right < heap.length
      · exact same left inside.1 right inside.2
      · constructor <;> intro related <;> exact False.elim (inside (related.refs_inside _ _ _ _))

theorem EqualAt.step_congr (heap : Heap) (first second : Nat)
    (same : ∀ left right, EqualAt first heap left right ↔ EqualAt second heap left right)
    (left right : Value) : EqualAt (first + 1) heap left right ↔ EqualAt (second + 1) heap left right := by
  have relation : EqualAt first heap = EqualAt second heap :=
    funext (fun left => funext (fun right => propext (same left right)))
  cases left <;> cases right <;> simp only [EqualAt, relation]

theorem EqualAt.equivalence (heap : Heap) (fuel : Nat) :
    EquivalenceBelow heap.length (fun left right => EqualAt (fuel + 1) heap (.ref left) (.ref right)) where
  reflexive _ inside := Or.inl ⟨rfl, ⟨_, List.getElem?_eq_getElem inside⟩⟩
  symmetric _ _ _ _ related := EqualAt.symm _ _ _ _ related
  transitive _ _ _ _ _ _ first second := EqualAt.trans _ _ _ _ _ first second

/-- Successful equalities stabilize already at the smaller linear bound, even for cyclic heaps. -/
theorem equalAt_stabilized (heap : Heap) (extra : Nat) (left right : Value) :
    EqualAt (heap.length + 1 + extra) heap left right ↔ EqualAt (heap.length + 1) heap left right := by
  have adjacent := finite_equivalence_stable heap.length
    (fun fuel left right => EqualAt (fuel + 1) heap (.ref left) (.ref right))
    (EqualAt.equivalence heap)
    (by
      intro fuel left _ right _ related
      apply (compare_equal_true_iff _ _ _ _).mp
      exact compare_step_extends heap (fuel + 1) true (.ref left) (.ref right) (.ok true)
        ((compare_equal_true_iff _ _ _ _).mpr related))
    (by
      intro fuel same left _ right _
      exact EqualAt.step_congr heap (fuel + 2) (fuel + 1)
        (EqualAt.positive_congr heap (fuel + 1) fuel same) (.ref left) (.ref right))
  have base := EqualAt.positive_congr heap (heap.length + 1) heap.length adjacent
  induction extra generalizing left right with
  | zero => exact Iff.rfl
  | succ extra ih =>
    exact (EqualAt.step_congr heap (heap.length + 1 + extra) (heap.length + 1) ih left right).trans (base left right)

theorem compare_equal_true_stabilized (heap : Heap) (extra : Nat) (left right : Value) :
    HeapSort.compare (heap.length + 1 + extra) heap true left right = some (.ok true) ↔
      HeapSort.compare (heap.length + 1) heap true left right = some (.ok true) := by
  simp only [compare_equal_true_iff, equalAt_stabilized]

/-- A true equality found at any depth is already found at the linear bound. -/
theorem compare_equal_true_linear_iff (heap : Heap) (left right : Value) :
    HeapSort.compare (heap.length + 1) heap true left right = some (.ok true) ↔
      ∃ fuel, HeapSort.compare fuel heap true left right = some (.ok true) := by
  constructor
  · intro compared
    exact ⟨_, compared⟩
  · rintro ⟨fuel, compared⟩
    have later := compare_extends heap fuel (heap.length + 1) true left right (.ok true) compared
    rw [Nat.add_comm] at later
    exact (compare_equal_true_stabilized heap fuel left right).mp later

/-- The runtime allowance captures every true equality found at any finite depth. -/
theorem compare_equal_true_native_iff (heap : Heap) (left right : Value) :
    HeapSort.compare (HeapSort.comparisonFuel heap) heap true left right = some (.ok true) ↔
      ∃ fuel, HeapSort.compare fuel heap true left right = some (.ok true) :=
  compare_stabilized_result_iff heap true left right (.ok true)

/-- Extra private objects cannot turn a non-true equality into true at native runtime fuel. -/
theorem RuntimeLayout.compare_equal_true_native {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (left right : Value) (leftInside : left.edge.Within logical.length) (rightInside : right.edge.Within logical.length) :
    HeapSort.compare (HeapSort.comparisonFuel physical) physical true (relocateValue rename left) (relocateValue rename right) =
        some (.ok true) ↔ HeapSort.compare (HeapSort.comparisonFuel logical) logical true left right = some (.ok true) := by
  constructor
  · intro compared
    rw [layout.compareFuel closed _ true left right leftInside rightInside] at compared
    exact (compare_equal_true_native_iff logical left right).mpr ⟨_, compared⟩
  · exact layout.compare_result closed true left right leftInside rightInside (.ok true)

theorem equalityOutcome_true_iff (outcome : HeapSort.Result Bool) (heap : Heap) (negate : Bool) :
    outcome.map (fun result => (result.map (fun equal => Value.scalar (.bool (if negate then !equal else equal))), heap)) =
        some (.ok (.scalar (.bool (!negate))), heap) ↔ outcome = some (.ok true) := by
  cases outcome with
  | none => simp
  | some result =>
    cases result with
    | error exception => simp [Except.map]
    | ok flag => cases negate <;> cases flag <;> simp [Except.map]

/-- Actual equality/inequality dispatch preserves a true underlying equality in both directions. -/
theorem RuntimeLayout.compare_equal_sequences_true {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (isTuple negate : Bool) (left right : Nat) (xs ys : List Value)
    (leftFound : logical[left]? = some (comparisonObject isTuple xs))
    (rightFound : logical[right]? = some (comparisonObject isTuple ys)) :
    HeapCalls.compare (if negate then .notEq else .eq) (.ref (rename left)) (.ref (rename right)) physical =
        some (.ok (.scalar (.bool (!negate))), physical) ↔
      HeapCalls.compare (if negate then .notEq else .eq) (.ref left) (.ref right) logical =
        some (.ok (.scalar (.bool (!negate))), logical) := by
  have movedLeft := layout.lookup left _ leftFound
  have movedRight := layout.lookup right _ rightFound
  rw [comparisonObject_relocates] at movedLeft movedRight
  rw [Relocation.compare_equal_sequences logical isTuple negate left right xs ys leftFound rightFound]
  rw [Relocation.compare_equal_sequences physical isTuple negate (rename left) (rename right) _ _ movedLeft movedRight]
  have leftInside := (List.getElem?_eq_some_iff.mp leftFound).1
  have rightInside := (List.getElem?_eq_some_iff.mp rightFound).1
  have same : rename left = rename right ↔ left = right :=
    ⟨layout.injective left leftInside right rightInside, congrArg rename⟩
  have leftBound : ∀ value ∈ xs, value.edge.Within logical.length := by
    have bounded := closed _ (List.mem_of_getElem? leftFound)
    cases isTuple <;> exact bounded
  have rightBound : ∀ value ∈ ys, value.edge.Within logical.length := by
    have bounded := closed _ (List.mem_of_getElem? rightFound)
    cases isTuple <;> exact bounded
  rw [equalLists_relocates logical.length rename layout.injective xs ys leftBound rightBound]
  simp only [same]
  cases shallow : (if left = right then some true else HeapCalls.equalLists xs ys) with
  | some flag => simp
  | none =>
    simp only [equalityOutcome_true_iff]
    exact layout.compare_equal_true_native closed (.ref left) (.ref right) leftInside rightInside

end FormalSW.PyAst.Mutable.Relocation
