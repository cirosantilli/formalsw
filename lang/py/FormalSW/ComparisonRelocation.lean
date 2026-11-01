import lang.py.FormalSW.KeyRelocation
import lang.py.FormalSW.HeapCalls

/-! Completed sequence comparisons survive relocation and extra private allocations. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

theorem lex_extends (equal less otherEqual otherLess : Value → Value → HeapSort.Result Bool)
    (equality : Bool) (xs ys : List Value)
    (equalExtends : ∀ x ∈ xs, ∀ y ∈ ys, ResolutionExtends (equal x y) (otherEqual x y))
    (lessExtends : ∀ x ∈ xs, ∀ y ∈ ys, ResolutionExtends (less x y) (otherLess x y)) :
    ResolutionExtends (HeapSort.lex equal less equality xs ys)
      (HeapSort.lex otherEqual otherLess equality xs ys) := by
  induction xs generalizing ys with
  | nil => cases ys <;> exact fun _ found => found
  | cons x xs ih =>
    cases ys with
    | nil => exact fun _ found => found
    | cons y ys =>
      intro result found
      cases first : equal x y with
      | none => simp [HeapSort.lex, first] at found
      | some outcome =>
        have same := equalExtends x (by simp) y (by simp) outcome first
        cases outcome with
        | error exception => simpa only [HeapSort.lex, first, same] using found
        | ok flag =>
          cases flag with
          | true =>
            simp only [HeapSort.lex, first, same] at found ⊢
            exact ih ys (fun a ha b hb => equalExtends a (by simp [ha]) b (by simp [hb]))
              (fun a ha b hb => lessExtends a (by simp [ha]) b (by simp [hb])) result found
          | false =>
            cases equality with
            | true => simpa only [HeapSort.lex, first, same, ↓reduceIte] using found
            | false =>
              simp only [HeapSort.lex, first, same, Bool.false_eq_true, ↓reduceIte] at found ⊢
              exact lessExtends x (by simp) y (by simp) result found

theorem lex_relocates (equal less otherEqual otherLess : Value → Value → HeapSort.Result Bool)
    (rename : Nat → Nat) (equality : Bool) (xs ys : List Value)
    (sameEqual : ∀ x ∈ xs, ∀ y ∈ ys,
      otherEqual (relocateValue rename x) (relocateValue rename y) = equal x y)
    (sameLess : ∀ x ∈ xs, ∀ y ∈ ys,
      otherLess (relocateValue rename x) (relocateValue rename y) = less x y) :
    HeapSort.lex otherEqual otherLess equality
        (xs.map (relocateValue rename)) (ys.map (relocateValue rename)) =
      HeapSort.lex equal less equality xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have first := sameEqual x (by simp) y (by simp)
      have order := sameLess x (by simp) y (by simp)
      have remaining := ih ys (fun a ha b hb => sameEqual a (by simp [ha]) b (by simp [hb]))
        (fun a ha b hb => sameLess a (by simp [ha]) b (by simp [hb]))
      simp only [List.map_cons, HeapSort.lex, first, order, remaining]

theorem compare_step_extends (heap : Heap) (fuel : Nat) (equality : Bool) (left right : Value) :
    ResolutionExtends (HeapSort.compare fuel heap equality left right)
      (HeapSort.compare (fuel + 1) heap equality left right) := by
  induction fuel generalizing equality left right with
  | zero => intro result found; cases found
  | succ fuel ih =>
    have sequences (same : Bool) (xs ys : List Value) :
        ResolutionExtends
          (if equality && same then some (.ok true)
           else if equality && xs.length != ys.length then some (.ok false)
           else HeapSort.lex (HeapSort.compare fuel heap true) (HeapSort.compare fuel heap false) equality xs ys)
          (if equality && same then some (.ok true)
           else if equality && xs.length != ys.length then some (.ok false)
           else HeapSort.lex (HeapSort.compare (fuel + 1) heap true)
             (HeapSort.compare (fuel + 1) heap false) equality xs ys) := by
      split
      · exact fun _ found => found
      · split
        · exact fun _ found => found
        · exact lex_extends _ _ _ _ equality xs ys
            (fun x _ y _ => ih true x y) (fun x _ y _ => ih false x y)
    cases left with
    | scalar left =>
      cases right with
      | scalar right => exact fun _ found => found
      | ref address =>
        cases found : heap[address]? with
        | none => exact fun _ found => found
        | some object => cases object <;> exact fun _ found => found
    | ref address =>
      cases right with
      | scalar right =>
        cases found : heap[address]? with
        | none => exact fun _ found => found
        | some object => cases object <;> exact fun _ found => found
      | ref other =>
        cases first : heap[address]? with
        | none => simp only [HeapSort.compare, first]; exact fun _ found => found
        | some leftObject =>
          cases second : heap[other]? with
          | none =>
            cases leftObject <;> simp only [HeapSort.compare, first, second] <;> exact fun _ found => found
          | some rightObject =>
            cases leftObject <;> cases rightObject <;>
              simp only [HeapSort.compare, first, second]
            all_goals first | exact sequences (address == other) _ _ | exact fun _ found => found

theorem compare_extends (heap : Heap) (fuel extra : Nat) (equality : Bool) (left right : Value) :
    ResolutionExtends (HeapSort.compare fuel heap equality left right)
      (HeapSort.compare (fuel + extra) heap equality left right) := by
  induction extra with
  | zero => exact fun _ found => found
  | succ extra ih =>
    intro result found
    exact compare_step_extends heap (fuel + extra) equality left right result (ih result found)

theorem RuntimeLayout.compareFuel {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (fuel : Nat) (equality : Bool) (left right : Value)
    (leftInside : left.edge.Within logical.length) (rightInside : right.edge.Within logical.length) :
    HeapSort.compare fuel physical equality (relocateValue rename left) (relocateValue rename right) =
      HeapSort.compare fuel logical equality left right := by
  induction fuel generalizing equality left right with
  | zero => rfl
  | succ fuel ih =>
    cases left with
    | scalar left =>
      cases right with
      | scalar right => rfl
      | ref address =>
        have found := List.getElem?_eq_getElem rightInside
        generalize objectValue : logical[address] = object at found
        have moved := layout.lookup address object found
        cases object <;> simp only [relocateValue, HeapSort.compare, found, moved, relocateObject]
    | ref address =>
      have first := List.getElem?_eq_getElem leftInside
      generalize objectValue : logical[address] = leftObject at first
      have movedFirst := layout.lookup address leftObject first
      cases right with
      | scalar right =>
        cases leftObject <;> simp only [relocateValue, HeapSort.compare, first, movedFirst, relocateObject]
      | ref other =>
        have second := List.getElem?_eq_getElem rightInside
        generalize otherValue : logical[other] = rightObject at second
        have movedSecond := layout.lookup other rightObject second
        have same : (rename address == rename other) = (address == other) := by
          apply Bool.eq_iff_iff.mpr
          simp only [beq_iff_eq]
          exact ⟨layout.injective address leftInside other rightInside, congrArg rename⟩
        have leftBound := closed leftObject (List.mem_of_getElem? first)
        have rightBound := closed rightObject (List.mem_of_getElem? second)
        have sequences (xs ys : List Value)
            (hx : ∀ value ∈ xs, value.edge.Within logical.length)
            (hy : ∀ value ∈ ys, value.edge.Within logical.length) :
            HeapSort.lex (HeapSort.compare fuel physical true) (HeapSort.compare fuel physical false)
                equality (xs.map (relocateValue rename)) (ys.map (relocateValue rename)) =
              HeapSort.lex (HeapSort.compare fuel logical true) (HeapSort.compare fuel logical false)
                equality xs ys :=
          lex_relocates _ _ _ _ rename equality xs ys
            (fun x hx' y hy' => ih true x y (hx x hx') (hy y hy'))
            (fun x hx' y hy' => ih false x y (hx x hx') (hy y hy'))
        cases leftObject <;> cases rightObject <;>
          simp only [relocateValue, HeapSort.compare, first, second, movedFirst, movedSecond,
            relocateObject, same, List.length_map]
        all_goals first
          | rfl
          | have transported := sequences _ _ leftBound rightBound
            simp only [objectValues] at transported
            rw [transported]

/-- Removing one source and its image leaves an injection into one fewer addresses. -/
theorem injective_below_le (source target : Nat) (rename : Nat → Nat)
    (injective : Graph.Relocation.InjectiveBelow rename source)
    (bounded : ∀ index < source, rename index < target) : source ≤ target := by
  induction source generalizing target rename with
  | zero => omega
  | succ source ih =>
    cases target with
    | zero => have impossible := bounded source (by omega); omega
    | succ target =>
      let reduced := fun index => if rename index < rename source then rename index else rename index - 1
      have distinct : ∀ index < source, rename index ≠ rename source := by
        intro index inside equal
        have same := injective index (by omega) source (by omega) equal
        omega
      have smaller : ∀ index < source, reduced index < target := by
        intro index inside
        have old := bounded index (by omega)
        have removed := bounded source (by omega)
        have different := distinct index inside
        dsimp only [reduced]
        split <;> omega
      have remains : Graph.Relocation.InjectiveBelow reduced source := by
        intro i hi j hj equal
        apply injective i (by omega) j (by omega)
        have first := distinct i hi
        have second := distinct j hj
        dsimp only [reduced] at equal
        split at equal <;> split at equal <;> omega
      have result := ih target reduced remains smaller
      omega

theorem RuntimeLayout.length_le {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) : logical.length ≤ physical.length :=
  injective_below_le logical.length physical.length rename layout.injective layout.bound

/-- The runtime uses each heap's own allowance. No acyclicity or fixed depth is assumed. -/
theorem RuntimeLayout.compare_result {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (equality : Bool) (left right : Value)
    (leftInside : left.edge.Within logical.length) (rightInside : right.edge.Within logical.length)
    (outcome : Except ExceptionObject Bool)
    (executed : HeapSort.compare (HeapSort.comparisonFuel logical) logical equality left right = some outcome) :
    HeapSort.compare (HeapSort.comparisonFuel physical) physical equality
      (relocateValue rename left) (relocateValue rename right) = some outcome := by
  have same := layout.compareFuel closed (HeapSort.comparisonFuel logical) equality left right leftInside rightInside
  rw [executed] at same
  have retained := compare_extends physical (HeapSort.comparisonFuel logical)
    (HeapSort.comparisonFuel physical - HeapSort.comparisonFuel logical)
    equality (relocateValue rename left) (relocateValue rename right) outcome same
  have size := HeapSort.comparisonFuel_mono logical physical layout.length_le
  have allowance : HeapSort.comparisonFuel logical +
      (HeapSort.comparisonFuel physical - HeapSort.comparisonFuel logical) = HeapSort.comparisonFuel physical := by omega
  simpa only [allowance] using retained

theorem sequenceCompare_eq (heap : Heap) (equality : Bool) (left right : Value) :
    HeapCalls.sequenceCompare equality left right heap =
      (HeapSort.compare (HeapSort.comparisonFuel heap) heap equality left right).map
        (fun result => (result.map (fun answer => Value.scalar (.bool answer)), heap)) := by
  cases compared : HeapSort.compare (HeapSort.comparisonFuel heap) heap equality left right with
  | none => simp [HeapCalls.sequenceCompare, eval_bind, compared, unsupported]
  | some outcome => cases outcome <;> simp [HeapCalls.sequenceCompare, eval_bind, compared, Except.map]

/-- Sequence comparison does not mutate memory, including when it raises. -/
theorem sequenceCompare_keeps_heap (heap after : Heap) (equality : Bool) (left right : Value)
    (outcome : Except ExceptionObject Value)
    (executed : HeapCalls.sequenceCompare equality left right heap = some (outcome, after)) : after = heap := by
  rw [sequenceCompare_eq] at executed
  cases compared : HeapSort.compare (HeapSort.comparisonFuel heap) heap equality left right with
  | none => simp [compared] at executed
  | some result =>
    simp only [compared, Option.map_some, Option.some.injEq, Prod.mk.injEq] at executed
    exact executed.2.symm

theorem RuntimeLayout.sequenceCompare {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (equality : Bool) (left right : Value)
    (leftInside : left.edge.Within logical.length) (rightInside : right.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : HeapCalls.sequenceCompare equality left right logical = some (outcome, after)) :
    HeapCalls.sequenceCompare equality (relocateValue rename left) (relocateValue rename right) physical =
      some (outcome.map (relocateValue rename), physical) := by
  rw [sequenceCompare_eq] at executed ⊢
  cases compared : HeapSort.compare (HeapSort.comparisonFuel logical) logical equality left right with
  | none => simp [compared] at executed
  | some result =>
    have other := layout.compare_result closed equality left right leftInside rightInside result compared
    rw [other]
    simp only [compared, Option.map_some, Option.some.injEq, Prod.mk.injEq] at executed
    rw [← executed.1]
    cases result <;> rfl

theorem ExecutionLayout.sequenceCompare {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (equality : Bool) (left right : Value)
    (leftInside : left.edge.Within logical.length) (rightInside : right.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : HeapCalls.sequenceCompare equality left right logical = some (outcome, after)) :
    HeapCalls.sequenceCompare equality (relocateValue rename left) (relocateValue rename right) physical =
        some (outcome.map (relocateValue rename), physical) ∧ ExecutionLayout after physical rename := by
  have same := sequenceCompare_keeps_heap logical after equality left right outcome executed
  exact ⟨layout.runtime.sequenceCompare layout.closed equality left right leftInside rightInside _ _ executed,
    same ▸ layout⟩

/-- A shared shape parameter for the two builtin sequence comparison branches. -/
def comparisonObject (isTuple : Bool) (items : List Value) : Object :=
  if isTuple then .tuple items else .list items

theorem comparisonObject_relocates (rename : Nat → Nat) (isTuple : Bool) (items : List Value) :
    relocateObject rename (comparisonObject isTuple items) =
      comparisonObject isTuple (items.map (relocateValue rename)) := by
  cases isTuple <;> rfl

theorem compare_order_sequences (heap : Heap) (isTuple reversed : Bool)
    (left right : Nat) (xs ys : List Value)
    (leftFound : heap[left]? = some (comparisonObject isTuple xs))
    (rightFound : heap[right]? = some (comparisonObject isTuple ys)) :
    HeapCalls.compare (if reversed then .gt else .lt) (.ref left) (.ref right) heap =
      HeapCalls.sequenceCompare false (if reversed then .ref right else .ref left)
        (if reversed then .ref left else .ref right) heap := by
  cases isTuple <;> cases reversed <;>
    simp [HeapCalls.compare, comparisonObject, Mutable.array, leftFound, rightFound, eval_bind]

/-- Transport actual Python `<` and `>` dispatch, including nested comparison exceptions. -/
theorem RuntimeLayout.compare_order_sequences {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (isTuple reversed : Bool) (left right : Nat) (xs ys : List Value)
    (leftFound : logical[left]? = some (comparisonObject isTuple xs))
    (rightFound : logical[right]? = some (comparisonObject isTuple ys))
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : HeapCalls.compare (if reversed then .gt else .lt) (.ref left) (.ref right) logical =
      some (outcome, after)) :
    HeapCalls.compare (if reversed then .gt else .lt) (.ref (rename left)) (.ref (rename right)) physical =
      some (outcome.map (relocateValue rename), physical) := by
  have movedLeft := layout.lookup left _ leftFound
  have movedRight := layout.lookup right _ rightFound
  rw [comparisonObject_relocates] at movedLeft movedRight
  rw [Relocation.compare_order_sequences logical isTuple reversed left right xs ys leftFound rightFound] at executed
  rw [Relocation.compare_order_sequences physical isTuple reversed (rename left) (rename right)
    _ _ movedLeft movedRight]
  have leftInside := (List.getElem?_eq_some_iff.mp leftFound).1
  have rightInside := (List.getElem?_eq_some_iff.mp rightFound).1
  cases reversed with
  | false => exact layout.sequenceCompare closed false (.ref left) (.ref right) leftInside rightInside _ _ executed
  | true => exact layout.sequenceCompare closed false (.ref right) (.ref left) rightInside leftInside _ _ executed

theorem equalElements_relocates (limit : Nat) (rename : Nat → Nat)
    (injective : Graph.Relocation.InjectiveBelow rename limit) (xs ys : List Value)
    (leftInside : ∀ value ∈ xs, value.edge.Within limit)
    (rightInside : ∀ value ∈ ys, value.edge.Within limit) :
    HeapCalls.equalElements (xs.map (relocateValue rename)) (ys.map (relocateValue rename)) =
      HeapCalls.equalElements xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have remaining := ih ys (fun value member => leftInside value (by simp [member]))
        (fun value member => rightInside value (by simp [member]))
      have hx := leftInside x (by simp)
      have hy := rightInside y (by simp)
      cases x with
      | scalar x =>
        cases y with
        | scalar y => simp only [List.map_cons, HeapCalls.equalElements, relocateValue, remaining]
        | ref y => rfl
      | ref x =>
        cases y with
        | scalar y => rfl
        | ref y =>
          have same : rename x = rename y ↔ x = y := ⟨injective x hx y hy, congrArg rename⟩
          simp only [List.map_cons, HeapCalls.equalElements, relocateValue, same, remaining]

theorem equalLists_relocates (limit : Nat) (rename : Nat → Nat)
    (injective : Graph.Relocation.InjectiveBelow rename limit) (xs ys : List Value)
    (leftInside : ∀ value ∈ xs, value.edge.Within limit)
    (rightInside : ∀ value ∈ ys, value.edge.Within limit) :
    HeapCalls.equalLists (xs.map (relocateValue rename)) (ys.map (relocateValue rename)) =
      HeapCalls.equalLists xs ys := by
  simp only [HeapCalls.equalLists, List.length_map,
    equalElements_relocates limit rename injective xs ys leftInside rightInside]

/-- Expose the actual identity/shallow-equality fast path and recursive fallback. -/
theorem compare_equal_sequences (heap : Heap) (isTuple negate : Bool)
    (left right : Nat) (xs ys : List Value)
    (leftFound : heap[left]? = some (comparisonObject isTuple xs))
    (rightFound : heap[right]? = some (comparisonObject isTuple ys)) :
    HeapCalls.compare (if negate then .notEq else .eq) (.ref left) (.ref right) heap =
      match (if left = right then some true else HeapCalls.equalLists xs ys) with
      | some equal => some (.ok (.scalar (.bool (if negate then !equal else equal))), heap)
      | none => (HeapSort.compare (HeapSort.comparisonFuel heap) heap true (.ref left) (.ref right)).map
          (fun outcome => (outcome.map (fun equal => Value.scalar (.bool (if negate then !equal else equal))), heap)) := by
  cases shallow : (if left = right then some true else HeapCalls.equalLists xs ys) with
  | some equal =>
    cases isTuple <;> cases negate <;>
      simp [HeapCalls.compare, comparisonObject, Mutable.array, leftFound, rightFound, eval_bind, shallow] <;> rfl
  | none =>
    cases recursive : HeapSort.compare (HeapSort.comparisonFuel heap) heap true (.ref left) (.ref right) with
    | none =>
      cases isTuple <;> cases negate <;>
        simp [HeapCalls.compare, comparisonObject, Mutable.array, leftFound, rightFound, eval_bind,
          shallow, HeapCalls.sequenceCompare, recursive, unsupported]
    | some outcome =>
      cases outcome <;> cases isTuple <;> cases negate <;>
        simp [HeapCalls.compare, comparisonObject, Mutable.array, leftFound, rightFound, eval_bind,
          shallow, HeapCalls.sequenceCompare, recursive, HeapCalls.unary, Mutable.truth, scalarTruth, Except.map]

theorem RuntimeLayout.compare_equal_sequences {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (isTuple negate : Bool) (left right : Nat) (xs ys : List Value)
    (leftFound : logical[left]? = some (comparisonObject isTuple xs))
    (rightFound : logical[right]? = some (comparisonObject isTuple ys))
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : HeapCalls.compare (if negate then .notEq else .eq) (.ref left) (.ref right) logical =
      some (outcome, after)) :
    HeapCalls.compare (if negate then .notEq else .eq) (.ref (rename left)) (.ref (rename right)) physical =
      some (outcome.map (relocateValue rename), physical) := by
  have movedLeft := layout.lookup left _ leftFound
  have movedRight := layout.lookup right _ rightFound
  rw [comparisonObject_relocates] at movedLeft movedRight
  rw [Relocation.compare_equal_sequences logical isTuple negate left right xs ys leftFound rightFound] at executed
  rw [Relocation.compare_equal_sequences physical isTuple negate (rename left) (rename right)
    _ _ movedLeft movedRight]
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
  | some equal =>
    simp only [shallow, Option.some.injEq, Prod.mk.injEq] at executed
    rw [← executed.1]
    rfl
  | none =>
    cases recursive : HeapSort.compare (HeapSort.comparisonFuel logical) logical true (.ref left) (.ref right) with
    | none => simp [shallow, recursive] at executed
    | some result =>
      have other := layout.compare_result closed true (.ref left) (.ref right) leftInside rightInside result recursive
      simp only [relocateValue] at other
      simp only [other]
      simp only [shallow, recursive, Option.map_some, Option.some.injEq, Prod.mk.injEq] at executed
      rw [← executed.1]
      cases result <;> rfl

end FormalSW.PyAst.Mutable.Relocation
