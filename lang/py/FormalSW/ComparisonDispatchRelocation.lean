import lang.py.FormalSW.ValueComparisonRelocation

/-! Complete builtin comparison dispatch and its read-only execution effect. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

def scalarComparisonAnswer (op : CmpOp) (left right : Constant) : HeapSort.Result Bool :=
  match scalarCompare op left right with
  | some answer => some (.ok answer)
  | none => HeapSort.typeError

theorem compareScalars_eq (heap : Heap) (op : CmpOp) (left right : Constant) :
    HeapCalls.compareScalars op left right heap = comparisonEval (scalarComparisonAnswer op left right) heap := by
  cases found : scalarCompare op left right <;> simp [HeapCalls.compareScalars, scalarComparisonAnswer,
    found, comparisonEval, HeapSort.typeError, error, Except.map]

theorem compareDifferent_eq (heap : Heap) (op : CmpOp) :
    HeapCalls.compareDifferent op heap = comparisonEval (equalityAnswer op (some false)) heap := by
  cases op <;> rfl

/-- The nonrecursive object branches. The outer `none` selects an existing specialized proof. -/
def simpleComparison (op : CmpOp) (same : Bool) : Object → Object → Option (HeapSort.Result Bool)
  | .bytearray xs, .bytearray ys => some (scalarComparisonAnswer op (.bytes xs) (.bytes ys))
  | .set xs, .set ys => some (some (.ok (ScalarSet.compare op xs ys)))
  | .set xs, .keySet ys => some (some (.ok (Mutable.compareKeySets op
      (xs.map fun x => (.scalar x, .scalar x)) ys)))
  | .keySet xs, other => some (match Mutable.keyEntries other with
      | some ys => some (.ok (Mutable.compareKeySets op xs ys))
      | none => equalityAnswer op (some false))
  | .instance _ _ _, .instance _ _ _ => some (equalityAnswer op (some same))
  | .list _, .list _ | .tuple _, .tuple _ | .dict _, .dict _ | .dict _, .keyDict _
  | .keyDict _, .dict _ | .keyDict _, .keyDict _ | .dataInstance .., .dataInstance .. => none
  | _, _ => some (equalityAnswer op (some false))

theorem simpleComparison_relocates (rename : Nat → Nat) (op : CmpOp) (same : Bool) (left right : Object) :
    simpleComparison op same (relocateObject rename left) (relocateObject rename right) =
      simpleComparison op same left right := by
  have sets (xs ys : List (HashKey × Value)) := compareKeySets_relocates rename op xs ys
  simp only [relocateKeyEntries] at sets
  have promoted (xs : List Constant) := promotedSet_relocates xs rename
  simp only [relocateKeyEntries] at promoted
  cases left <;> cases right <;> simp only [relocateObject, simpleComparison, Mutable.keyEntries]
  all_goals first
    | rfl
    | rw [sets]
    | rw [← promoted, sets]; simp only [promoted]

theorem simpleComparison_eq (heap : Heap) (op : CmpOp) (a b : Nat) (left right : Object)
    (first : heap[a]? = some left) (second : heap[b]? = some right) (answer : HeapSort.Result Bool)
    (classified : simpleComparison op (a == b) left right = some answer) :
    HeapCalls.compare op (.ref a) (.ref b) heap = comparisonEval answer heap := by
  simp only [HeapCalls.compare, eval_bind, eval_get]
  dsimp only [bind, Option.bind]
  rw [first, second]
  cases left <;> cases right <;> simp only [simpleComparison, Mutable.keyEntries, Option.some.injEq] at classified
  all_goals first
    | contradiction
    | subst answer
      first
        | rfl
        | exact compareScalars_eq heap op _ _
        | exact compareDifferent_eq heap op
        | cases op <;> rfl

theorem compare_scalar_ref_eq (heap : Heap) (op : CmpOp) (left : Constant) (address : Nat) (object : Object)
    (found : heap[address]? = some object) :
    HeapCalls.compare op (.scalar left) (.ref address) heap =
      match left, object with
      | .bytes xs, .bytearray ys => comparisonEval (scalarComparisonAnswer op (.bytes xs) (.bytes ys)) heap
      | _, _ => comparisonEval (equalityAnswer op (some false)) heap := by
  simp only [HeapCalls.compare, eval_bind, eval_get]
  dsimp only [bind, Option.bind]
  conv => lhs; rw [found]
  cases left <;> cases object
  all_goals first | exact compareScalars_eq heap op _ _ | exact compareDifferent_eq heap op

theorem compare_ref_scalar_eq (heap : Heap) (op : CmpOp) (address : Nat) (right : Constant) (object : Object)
    (found : heap[address]? = some object) :
    HeapCalls.compare op (.ref address) (.scalar right) heap =
      match object, right with
      | .bytearray xs, .bytes ys => comparisonEval (scalarComparisonAnswer op (.bytes xs) (.bytes ys)) heap
      | _, _ => comparisonEval (equalityAnswer op (some false)) heap := by
  simp only [HeapCalls.compare, eval_bind, eval_get]
  dsimp only [bind, Option.bind]
  conv => lhs; rw [found]
  cases right <;> cases object
  all_goals first | exact compareScalars_eq heap op _ _ | exact compareDifferent_eq heap op

theorem RuntimeLayout.compare_sequences {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (isTuple : Bool) (op : CmpOp) (a b : Nat) (xs ys : List Value)
    (first : logical[a]? = some (comparisonObject isTuple xs))
    (second : logical[b]? = some (comparisonObject isTuple ys))
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : HeapCalls.compare op (.ref a) (.ref b) logical = some (outcome, after)) :
    HeapCalls.compare op (.ref (rename a)) (.ref (rename b)) physical =
      some (outcome.map (relocateValue rename), physical) := by
  cases op with
  | eq => exact layout.compare_equal_sequences closed isTuple false a b xs ys first second _ _ executed
  | notEq => exact layout.compare_equal_sequences closed isTuple true a b xs ys first second _ _ executed
  | lt => exact layout.compare_order_sequences closed isTuple false a b xs ys first second _ _ executed
  | gt => exact layout.compare_order_sequences closed isTuple true a b xs ys first second _ _ executed
  | ltE | gtE =>
    cases isTuple <;> simp [HeapCalls.compare, comparisonObject, first, second, Mutable.array, unsupported] at executed

/-- Every completed builtin comparison transports at the actual runtime allowances. -/
theorem RuntimeLayout.compare {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (op : CmpOp) (left right : Value)
    (leftInside : left.edge.Within logical.length) (rightInside : right.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : HeapCalls.compare op left right logical = some (outcome, after)) :
    HeapCalls.compare op (relocateValue rename left) (relocateValue rename right) physical =
      some (outcome.map (relocateValue rename), physical) := by
  have transport (same : HeapCalls.compare op (relocateValue rename left) (relocateValue rename right) physical =
      (HeapCalls.compare op left right logical).map (fun pair => (pair.1.map (relocateValue rename), physical))) :
      HeapCalls.compare op (relocateValue rename left) (relocateValue rename right) physical =
        some (outcome.map (relocateValue rename), physical) := by rw [same, executed]; rfl
  cases left with
  | scalar scalar =>
    cases right with
    | scalar other =>
      apply transport
      change HeapCalls.compareScalars op scalar other physical = (HeapCalls.compareScalars op scalar other logical).map _
      rw [compareScalars_eq, compareScalars_eq]
      exact comparisonEval_relocates _ logical physical rename
    | ref address =>
      have found := List.getElem?_eq_getElem rightInside
      generalize objectValue : logical[address] = object at found
      have moved := layout.lookup address object found
      apply transport
      change HeapCalls.compare op (.scalar scalar) (.ref (rename address)) physical = _
      rw [compare_scalar_ref_eq logical op scalar address object found,
        compare_scalar_ref_eq physical op scalar (rename address) _ moved]
      cases scalar <;> cases object <;> exact comparisonEval_relocates _ logical physical rename
  | ref address =>
    have first := List.getElem?_eq_getElem leftInside
    generalize objectValue : logical[address] = object at first
    have movedFirst := layout.lookup address object first
    cases right with
    | scalar scalar =>
      apply transport
      change HeapCalls.compare op (.ref (rename address)) (.scalar scalar) physical = _
      rw [compare_ref_scalar_eq logical op address scalar object first,
        compare_ref_scalar_eq physical op (rename address) scalar _ movedFirst]
      cases scalar <;> cases object <;> exact comparisonEval_relocates _ logical physical rename
    | ref other =>
      have second := List.getElem?_eq_getElem rightInside
      generalize otherValue : logical[other] = otherObject at second
      have movedSecond := layout.lookup other otherObject second
      have identity : (rename address == rename other) = (address == other) := by
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq]
        exact ⟨layout.injective address leftInside other rightInside, congrArg rename⟩
      cases classified : simpleComparison op (address == other) object otherObject with
      | some answer =>
        have otherClassified : simpleComparison op (rename address == rename other)
            (relocateObject rename object) (relocateObject rename otherObject) = some answer := by
          rw [identity, simpleComparison_relocates, classified]
        apply transport
        change HeapCalls.compare op (.ref (rename address)) (.ref (rename other)) physical = _
        rw [simpleComparison_eq logical op address other object otherObject first second answer classified,
          simpleComparison_eq physical op (rename address) (rename other) _ _ movedFirst movedSecond answer otherClassified]
        exact comparisonEval_relocates _ logical physical rename
      | none =>
        cases object <;> cases otherObject <;> simp only [simpleComparison, Mutable.keyEntries] at classified
        all_goals first
          | contradiction
          | exact layout.compare_sequences closed false op address other _ _ first second _ _ executed
          | exact layout.compare_sequences closed true op address other _ _ first second _ _ executed
          | exact transport (layout.compare_dicts closed op address other _ _ first second)
          | exact transport (layout.compare_dict_keyDict closed op address other _ _ first second)
          | exact transport (layout.compare_keyDict closed op address other _ _ _ first second rfl)
          | exact transport (layout.compare_dataInstances closed op address other _ _ _ _ _ _ _ _ _ _ first second)

theorem compare_sequences_readonly (heap : Heap) (isTuple : Bool) (op : CmpOp)
    (a b : Nat) (xs ys : List Value)
    (first : heap[a]? = some (comparisonObject isTuple xs))
    (second : heap[b]? = some (comparisonObject isTuple ys)) :
    ∃ result, HeapCalls.compare op (.ref a) (.ref b) heap = comparisonEval result heap := by
  cases op with
  | eq =>
    have source := compare_equal_sequences heap isTuple false a b xs ys first second
    simp only [Bool.false_eq_true, ↓reduceIte] at source
    rw [source]
    cases shallow : (if a = b then some true else HeapCalls.equalLists xs ys) with
    | some answer => exact ⟨some (.ok answer), rfl⟩
    | none => exact ⟨HeapSort.compare (HeapSort.comparisonFuel heap) heap true (.ref a) (.ref b), rfl⟩
  | notEq =>
    have source := compare_equal_sequences heap isTuple true a b xs ys first second
    simp only [↓reduceIte] at source
    rw [source]
    cases shallow : (if a = b then some true else HeapCalls.equalLists xs ys) with
    | some answer => exact ⟨some (.ok (!answer)), rfl⟩
    | none =>
      refine ⟨(HeapSort.compare (HeapSort.comparisonFuel heap) heap true (.ref a) (.ref b)).map (Except.map Bool.not), ?_⟩
      cases HeapSort.compare (HeapSort.comparisonFuel heap) heap true (.ref a) (.ref b) with
      | none => rfl
      | some outcome => cases outcome <;> rfl
  | lt =>
    have source := compare_order_sequences heap isTuple false a b xs ys first second
    simp only [Bool.false_eq_true, ↓reduceIte] at source
    exact ⟨_, source.trans (sequenceCompare_eq heap false (.ref a) (.ref b))⟩
  | gt =>
    have source := compare_order_sequences heap isTuple true a b xs ys first second
    simp only [↓reduceIte] at source
    exact ⟨_, source.trans (sequenceCompare_eq heap false (.ref b) (.ref a))⟩
  | ltE | gtE =>
    refine ⟨none, ?_⟩
    cases isTuple <;> simp [HeapCalls.compare, comparisonObject, first, second, Mutable.array, unsupported, comparisonEval]

/-- Builtin comparisons never return references or mutate the heap, even on modeled failure. -/
theorem compare_readonly (heap : Heap) (op : CmpOp) (left right : Value)
    (leftInside : left.edge.Within heap.length) (rightInside : right.edge.Within heap.length) :
    ∃ result, HeapCalls.compare op left right heap = comparisonEval result heap := by
  cases left with
  | scalar scalar =>
    cases right with
    | scalar other => exact ⟨_, compareScalars_eq heap op scalar other⟩
    | ref address =>
      have found := List.getElem?_eq_getElem rightInside
      generalize objectValue : heap[address] = object at found
      rw [compare_scalar_ref_eq heap op scalar address object found]
      cases scalar <;> cases object <;> exact ⟨_, rfl⟩
  | ref address =>
    have first := List.getElem?_eq_getElem leftInside
    generalize objectValue : heap[address] = object at first
    cases right with
    | scalar scalar =>
      rw [compare_ref_scalar_eq heap op address scalar object first]
      cases scalar <;> cases object <;> exact ⟨_, rfl⟩
    | ref other =>
      have second := List.getElem?_eq_getElem rightInside
      generalize otherValue : heap[other] = otherObject at second
      cases classified : simpleComparison op (address == other) object otherObject with
      | some answer => exact ⟨answer, simpleComparison_eq heap op address other object otherObject first second answer classified⟩
      | none =>
        cases object <;> cases otherObject <;> simp only [simpleComparison, Mutable.keyEntries] at classified
        all_goals first
          | contradiction
          | exact compare_sequences_readonly heap false op address other _ _ first second
          | exact compare_sequences_readonly heap true op address other _ _ first second
          | exact ⟨_, compare_dicts_eq heap op address other _ _ first second⟩
          | exact ⟨_, compare_dict_keyDict_eq heap op address other _ _ first second⟩
          | exact ⟨_, compare_keyDict_eq heap op address other _ _ _ first second rfl⟩
          | rw [compare_dataInstances_eq heap op address other _ _ _ _ _ _ _ _ _ _ first second]
            split
            · exact ⟨_, compareDifferent_eq heap op⟩
            · split
              · exact ⟨none, rfl⟩
              · exact ⟨_, rfl⟩

theorem compare_effect (heap after : Heap) (op : CmpOp) (left right : Value)
    (leftInside : left.edge.Within heap.length) (rightInside : right.edge.Within heap.length)
    (outcome : Except ExceptionObject Value)
    (executed : HeapCalls.compare op left right heap = some (outcome, after)) :
    ∃ result : Except ExceptionObject Bool,
      outcome = result.map (fun answer => Value.scalar (.bool answer)) ∧ after = heap := by
  obtain ⟨result, equal⟩ := compare_readonly heap op left right leftInside rightInside
  rw [equal] at executed
  cases result with
  | none => cases executed
  | some result =>
    have same := Prod.mk.inj (Option.some.inj executed)
    exact ⟨result, same.1.symm, same.2.symm⟩

theorem ExecutionLayout.compare {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (op : CmpOp) (left right : Value)
    (leftInside : left.edge.Within logical.length) (rightInside : right.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : HeapCalls.compare op left right logical = some (outcome, after)) :
    HeapCalls.compare op (relocateValue rename left) (relocateValue rename right) physical =
        some (outcome.map (relocateValue rename), physical) ∧ ExecutionLayout after physical rename ∧
      (∀ value, outcome = .ok value → value.edge.Within after.length) := by
  obtain ⟨result, same, unchanged⟩ := compare_effect logical after op left right leftInside rightInside outcome executed
  refine ⟨layout.runtime.compare layout.closed op left right leftInside rightInside _ _ executed, unchanged ▸ layout, ?_⟩
  intro value success
  rw [same] at success
  cases result with
  | error exception => cases success
  | ok answer => cases success; trivial

end FormalSW.PyAst.Mutable.Relocation
