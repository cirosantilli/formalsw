import lang.py.FormalSW.ComparisonUnsupported
import lang.py.FormalSW.ComparisonStability

/-! All primitive comparison outcomes survive address relocation and private allocations. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

/-- Every previously completed fuel-indexed comparison retains its exact runtime result. -/
theorem compare_native_result (heap : Heap) (fuel : Nat) (equality : Bool) (left right : Value)
    (outcome : Except ExceptionObject Bool)
    (completed : HeapSort.compare fuel heap equality left right = some outcome) :
    HeapSort.compare (HeapSort.comparisonFuel heap) heap equality left right = some outcome :=
  (compare_stabilized_result_iff heap equality left right outcome).mpr ⟨fuel, completed⟩

/-- Runtime exhaustion means that no finite unfolding can resolve the comparison. -/
theorem compare_native_unsupported_iff (heap : Heap) (equality : Bool) (left right : Value) :
    HeapSort.compare (HeapSort.comparisonFuel heap) heap equality left right = none ↔
      ∀ fuel, HeapSort.compare fuel heap equality left right = none :=
  compare_stabilized_none_iff heap equality left right

theorem RuntimeLayout.compare_native {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (equality : Bool) (left right : Value)
    (leftInside : left.edge.Within logical.length) (rightInside : right.edge.Within logical.length) :
    HeapSort.compare (HeapSort.comparisonFuel physical) physical equality
        (relocateValue rename left) (relocateValue rename right) =
      HeapSort.compare (HeapSort.comparisonFuel logical) logical equality left right :=
  layout.compare_stabilized closed equality left right leftInside rightInside

theorem RuntimeLayout.sequenceCompare_complete {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (equality : Bool) (left right : Value)
    (leftInside : left.edge.Within logical.length) (rightInside : right.edge.Within logical.length) :
    HeapCalls.sequenceCompare equality (relocateValue rename left) (relocateValue rename right) physical =
      (HeapCalls.sequenceCompare equality left right logical).map
        (fun pair => (pair.1.map (relocateValue rename), physical)) := by
  rw [sequenceCompare_eq, sequenceCompare_eq,
    layout.compare_native closed equality left right leftInside rightInside]
  cases HeapSort.compare (HeapSort.comparisonFuel logical) logical equality left right with
  | none => rfl
  | some outcome => cases outcome <;> rfl

theorem RuntimeLayout.compare_equal_sequences_complete {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (isTuple negate : Bool) (left right : Nat) (xs ys : List Value)
    (first : logical[left]? = some (comparisonObject isTuple xs))
    (second : logical[right]? = some (comparisonObject isTuple ys)) :
    HeapCalls.compare (if negate then .notEq else .eq) (.ref (rename left)) (.ref (rename right)) physical =
      (HeapCalls.compare (if negate then .notEq else .eq) (.ref left) (.ref right) logical).map
        (fun pair => (pair.1.map (relocateValue rename), physical)) := by
  have movedFirst := layout.lookup left _ first
  have movedSecond := layout.lookup right _ second
  rw [comparisonObject_relocates] at movedFirst movedSecond
  rw [Relocation.compare_equal_sequences logical isTuple negate left right xs ys first second,
    Relocation.compare_equal_sequences physical isTuple negate (rename left) (rename right) _ _ movedFirst movedSecond]
  have leftInside := (List.getElem?_eq_some_iff.mp first).1
  have rightInside := (List.getElem?_eq_some_iff.mp second).1
  have same : rename left = rename right ↔ left = right :=
    ⟨layout.injective left leftInside right rightInside, congrArg rename⟩
  have leftBound : ∀ value ∈ xs, value.edge.Within logical.length := by
    have bounded := closed _ (List.mem_of_getElem? first)
    cases isTuple <;> exact bounded
  have rightBound : ∀ value ∈ ys, value.edge.Within logical.length := by
    have bounded := closed _ (List.mem_of_getElem? second)
    cases isTuple <;> exact bounded
  rw [equalLists_relocates logical.length rename layout.injective xs ys leftBound rightBound]
  simp only [same]
  cases tested : (if left = right then some true else HeapCalls.equalLists xs ys) with
  | some answer => rfl
  | none =>
    have compared := layout.compare_native closed true (.ref left) (.ref right) leftInside rightInside
    simp only [relocateValue] at compared
    rw [compared]
    cases HeapSort.compare (HeapSort.comparisonFuel logical) logical true (.ref left) (.ref right) with
    | none => rfl
    | some outcome => cases outcome <;> rfl

theorem RuntimeLayout.compare_sequences_complete {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (isTuple : Bool) (op : CmpOp) (left right : Nat) (xs ys : List Value)
    (first : logical[left]? = some (comparisonObject isTuple xs))
    (second : logical[right]? = some (comparisonObject isTuple ys)) :
    HeapCalls.compare op (.ref (rename left)) (.ref (rename right)) physical =
      (HeapCalls.compare op (.ref left) (.ref right) logical).map
        (fun pair => (pair.1.map (relocateValue rename), physical)) := by
  have movedFirst := layout.lookup left _ first
  have movedSecond := layout.lookup right _ second
  have leftInside := (List.getElem?_eq_some_iff.mp first).1
  have rightInside := (List.getElem?_eq_some_iff.mp second).1
  cases op with
  | eq => exact layout.compare_equal_sequences_complete closed isTuple false left right xs ys first second
  | notEq => exact layout.compare_equal_sequences_complete closed isTuple true left right xs ys first second
  | lt =>
    rw [comparisonObject_relocates] at movedFirst movedSecond
    have firstEq := Relocation.compare_order_sequences logical isTuple false left right xs ys first second
    have secondEq := Relocation.compare_order_sequences physical isTuple false (rename left) (rename right) _ _ movedFirst movedSecond
    simp only [Bool.false_eq_true, ↓reduceIte] at firstEq secondEq
    rw [firstEq, secondEq]
    exact layout.sequenceCompare_complete closed false (.ref left) (.ref right) leftInside rightInside
  | gt =>
    rw [comparisonObject_relocates] at movedFirst movedSecond
    have firstEq := Relocation.compare_order_sequences logical isTuple true left right xs ys first second
    have secondEq := Relocation.compare_order_sequences physical isTuple true (rename left) (rename right) _ _ movedFirst movedSecond
    simp only [↓reduceIte] at firstEq secondEq
    rw [firstEq, secondEq]
    exact layout.sequenceCompare_complete closed false (.ref right) (.ref left) rightInside leftInside
  | ltE | gtE =>
    cases isTuple <;> simp [HeapCalls.compare, comparisonObject, first, second, movedFirst, movedSecond,
      relocateObject, Mutable.array, unsupported]

theorem RuntimeLayout.compare_complete {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (op : CmpOp) (left right : Value)
    (leftInside : left.edge.Within logical.length) (rightInside : right.edge.Within logical.length) :
    HeapCalls.compare op (relocateValue rename left) (relocateValue rename right) physical =
      (HeapCalls.compare op left right logical).map
        (fun pair => (pair.1.map (relocateValue rename), physical)) := by
  cases left with
  | scalar scalar =>
    cases right with
    | scalar other =>
      change HeapCalls.compareScalars op scalar other physical = (HeapCalls.compareScalars op scalar other logical).map _
      rw [compareScalars_eq, compareScalars_eq]
      exact comparisonEval_relocates _ logical physical rename
    | ref address =>
      have found := List.getElem?_eq_getElem rightInside
      generalize objectValue : logical[address] = object at found
      have moved := layout.lookup address object found
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
        change HeapCalls.compare op (.ref (rename address)) (.ref (rename other)) physical = _
        rw [simpleComparison_eq logical op address other object otherObject first second answer classified,
          simpleComparison_eq physical op (rename address) (rename other) _ _ movedFirst movedSecond answer otherClassified]
        exact comparisonEval_relocates _ logical physical rename
      | none =>
        cases object <;> cases otherObject <;>
          simp only [simpleComparison, Mutable.keyEntries] at classified
        all_goals first
          | contradiction
          | exact layout.compare_sequences_complete closed false op address other _ _ first second
          | exact layout.compare_sequences_complete closed true op address other _ _ first second
          | exact layout.compare_dicts closed op address other _ _ first second
          | exact layout.compare_dict_keyDict closed op address other _ _ first second
          | exact layout.compare_keyDict closed op address other _ _ _ first second rfl
          | exact layout.compare_dataInstances closed op address other _ _ _ _ _ _ _ _ _ _ first second


end FormalSW.PyAst.Mutable.Relocation
