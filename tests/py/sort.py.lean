import «.cleanxy».tests.py.«sort.py.ast»
import CleanXY

namespace tests.py.sort

open CleanXY.PyAst

private def sameValueKind : Value → Value → Prop
  | .int _, .int _ => True
  | .string _, .string _ => True
  | .object leftType _, .object rightType _ => leftType = rightType
  | _, _ => False

private theorem sameValueKind_of_lt_ok {left right : Value} {result : Bool}
    (h : evalValueCmp .lt left right = .ok result) :
    sameValueKind left right := by
  cases left with
  | int left =>
      cases right with
      | int right => simp [sameValueKind]
      | string right => simp [evalValueCmp] at h
      | object rightType right => simp [evalValueCmp] at h
  | string left =>
      cases right with
      | int right => simp [evalValueCmp] at h
      | string right => simp [sameValueKind]
      | object rightType right => simp [evalValueCmp] at h
  | object leftType left =>
      cases right with
      | int right => simp [evalValueCmp] at h
      | string right => simp [evalValueCmp] at h
      | object rightType right =>
          by_cases same : leftType = rightType
          · simpa [sameValueKind] using same
          · simp [evalValueCmp, same] at h

private theorem ltE_ok_of_sameValueKind {left right : Value}
    (h : sameValueKind left right) :
    ∃ result, evalValueCmp .ltE left right = .ok result := by
  cases left with
  | int left =>
      cases right with
      | int right => simp [evalValueCmp]
      | string right => simp [sameValueKind] at h
      | object rightType right => simp [sameValueKind] at h
  | string left =>
      cases right with
      | int right => simp [sameValueKind] at h
      | string right => simp [evalValueCmp]
      | object rightType right => simp [sameValueKind] at h
  | object leftType left =>
      cases right with
      | int right => simp [sameValueKind] at h
      | string right => simp [sameValueKind] at h
      | object rightType right =>
          simp only [sameValueKind] at h
          subst rightType
          simp [evalValueCmp]

private theorem mergeSortedFuel_safe :
    ∀ fuel left right,
      (∀ leftValue ∈ left, ∀ rightValue ∈ right,
        sameValueKind leftValue rightValue) →
      ∃ result,
        mergeSortedFuel fuel left right = .ok result ∧
        ∀ value ∈ result, value ∈ left ∨ value ∈ right := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right _
      refine ⟨left ++ right, rfl, ?_⟩
      simp
  | succ fuel ih =>
      intro left right safe
      cases left with
      | nil => exact ⟨right, rfl, by simp⟩
      | cons leftHead leftTail =>
        cases right with
        | nil => exact ⟨leftHead :: leftTail, rfl, by simp⟩
        | cons rightHead rightTail =>
          obtain ⟨comparison, comparison_eq⟩ :=
            ltE_ok_of_sameValueKind (safe leftHead (by simp) rightHead (by simp))
          cases comparison with
          | false =>
              obtain ⟨result, result_eq, result_mem⟩ :=
                ih (leftHead :: leftTail) rightTail (by
                  intro leftValue leftMem rightValue rightMem
                  exact safe leftValue leftMem rightValue (by simp [rightMem]))
              rw [mergeSortedFuel, comparison_eq, result_eq]
              refine ⟨rightHead :: result, rfl, ?_⟩
              intro value valueMem
              simp only [List.mem_cons] at valueMem
              rcases valueMem with rfl | valueMem
              · exact .inr (by simp)
              · rcases result_mem value valueMem with leftMem | rightMem
                · exact .inl leftMem
                · exact .inr (by simp [rightMem])
          | true =>
              obtain ⟨result, result_eq, result_mem⟩ :=
                ih leftTail (rightHead :: rightTail) (by
                  intro leftValue leftMem rightValue rightMem
                  exact safe leftValue (by simp [leftMem]) rightValue rightMem)
              rw [mergeSortedFuel, comparison_eq, result_eq]
              refine ⟨leftHead :: result, rfl, ?_⟩
              intro value valueMem
              simp only [List.mem_cons] at valueMem
              rcases valueMem with rfl | valueMem
              · exact .inl (by simp)
              · rcases result_mem value valueMem with leftMem | rightMem
                · exact .inl (by simp [leftMem])
                · exact .inr rightMem

private theorem evalMergeSortFuel_safe :
    ∀ fuel values,
      (∀ left ∈ values, ∀ right ∈ values, sameValueKind left right) →
      ∃ result,
        evalMergeSortFuel fuel values = .ok result ∧
        ∀ value ∈ result, value ∈ values := by
  intro fuel
  induction fuel with
  | zero =>
      intro values _
      exact ⟨values, rfl, by simp⟩
  | succ fuel ih =>
      intro values safe
      by_cases short : values.length ≤ 1
      · exact ⟨values, by simp [evalMergeSortFuel, short], by simp⟩
      · let middle := values.length / 2
        obtain ⟨left, left_eq, left_mem⟩ := ih (values.take middle) (by
          intro a ha b hb
          exact safe a (List.mem_of_mem_take ha) b (List.mem_of_mem_take hb))
        obtain ⟨right, right_eq, right_mem⟩ := ih (values.drop middle) (by
          intro a ha b hb
          exact safe a (List.mem_of_mem_drop ha) b (List.mem_of_mem_drop hb))
        obtain ⟨result, result_eq, result_mem⟩ :=
          mergeSortedFuel_safe values.length left right (by
            intro a ha b hb
            exact safe a (List.mem_of_mem_take (left_mem a ha))
              b (List.mem_of_mem_drop (right_mem b hb)))
        refine ⟨result, ?_, ?_⟩
        · rw [evalMergeSortFuel]
          simp only [short, ↓reduceIte]
          rw [left_eq]
          rw [right_eq]
          exact result_eq
        · intro value valueMem
          rcases result_mem value valueMem with leftValue | rightValue
          · exact List.mem_of_mem_take (left_mem value leftValue)
          · exact List.mem_of_mem_drop (right_mem value rightValue)

/-- The integer-only sorting implementations have the same result. -/
theorem merge_sort_int.«Equiv(quick_sort_int)» :
    CleanXY.Property.Function.Equiv
      SortAst.module "merge_sort_int" "quick_sort_int" := by
  apply CleanXY.PyAst.canonicalSort_equiv
  · intro values
    rfl
  · intro values
    rfl

/-- Integer merge sort has linearithmic worst-case cost. -/
theorem merge_sort_int.«BigO(n * (Nat.log2 n + 1), n = len(values))» :
    CleanXY.Property.Function.BigO
      SortAst.module "merge_sort_int" (.listLength "values")
        (fun n => n * (Nat.log2 n + 1)) := by
  apply CleanXY.Property.Function.bigO_of_growth_bound
    (inputSize := .listLength "values") (growth := .linearithmic)
  · rfl
  · rfl
  · exact CleanXY.PyAst.Growth.linearithmic_isBigO

/-- Integer first-element-pivot quicksort has quadratic worst-case cost. -/
theorem quick_sort_int.«BigO(n * n, n = len(values))» :
    CleanXY.Property.Function.BigO
      SortAst.module "quick_sort_int" (.listLength "values") (fun n => n * n) := by
  apply CleanXY.Property.Function.bigO_of_growth_bound
    (inputSize := .listLength "values") (growth := .quadratic)
  · rfl
  · rfl
  · exact CleanXY.PyAst.Growth.quadratic_isBigO

/-- Sorting the one-integer wrapper factors through the integer sort model. -/
theorem merge_sort_dummy_int.«Equiv(quick_sort_dummy_int)» :
    CleanXY.Property.Function.Equiv
      SortAst.module "merge_sort_dummy_int" "quick_sort_dummy_int" := by
  apply CleanXY.PyAst.canonicalSort_equiv
  · intro values
    rfl
  · intro values
    rfl

/-- A mixed integer/string input makes untyped merge sort throw. -/
theorem merge_sort_untyped.«Throws» :
    CleanXY.Property.Function.Throws
      SortAst.module "merge_sort_untyped" := by
  refine ⟨[.int 0, .string []], {
    typeName := "TypeError"
    args := [.string "'<=' not supported between instances of 'int' and 'str'"]
  }, ?_⟩
  rfl

/-- Untyped merge sort succeeds when `<` is defined for every input pair. -/
theorem merge_sort_untyped_not_throws_of_lt_safe
    (values : List Value)
    (_safe : ∀ left ∈ values, ∀ right ∈ values,
      ∃ result, evalValueCmp .lt left right = .ok result) :
    ∃ result, evalUnaryListFunctionOutcome
      SortAst.module "merge_sort_untyped" values = some (.ok result) := by
  have homogeneous :
      ∀ left ∈ values, ∀ right ∈ values, sameValueKind left right := by
    intro left leftMem right rightMem
    obtain ⟨comparison, comparison_eq⟩ := _safe left leftMem right rightMem
    exact sameValueKind_of_lt_ok comparison_eq
  obtain ⟨result, result_eq, _⟩ :=
    evalMergeSortFuel_safe values.length values homogeneous
  refine ⟨canonicalValueSort values, ?_⟩
  change some (normalizeSortOutcome values
    (evalMergeSortFuel values.length values)) = some (.ok (canonicalValueSort values))
  rw [result_eq]
  rfl

/-- The generic untyped semantics also sort comparable modeled objects. -/
example :
    evalUnaryListFunctionOutcome SortAst.module "merge_sort_untyped"
      [.object "DummyInt" 2, .object "DummyInt" 1] =
        some (.ok [.object "DummyInt" 1, .object "DummyInt" 2]) := by
  rfl

/-- Whenever both untyped sorting implementations return, their results agree. -/
theorem merge_sort_untyped.«EquivReturn(quick_sort)» :
    CleanXY.Property.Function.EquivReturn
      SortAst.module "merge_sort_untyped" "quick_sort" := by
  intro values leftResult rightResult leftOutcome rightOutcome
  change some (CleanXY.PyAst.normalizeSortOutcome values
      (CleanXY.PyAst.evalMergeSortFuel values.length values)) =
    some (.ok leftResult) at leftOutcome
  change some (CleanXY.PyAst.normalizeSortOutcome values
      (CleanXY.PyAst.evalQuickSortFuel values.length values)) =
    some (.ok rightResult) at rightOutcome
  cases mergeRun : CleanXY.PyAst.evalMergeSortFuel values.length values <;>
    cases quickRun : CleanXY.PyAst.evalQuickSortFuel values.length values <;>
    simp [
      mergeRun,
      quickRun,
      CleanXY.PyAst.normalizeSortOutcome,
    ] at leftOutcome rightOutcome
  exact leftOutcome.symm.trans rightOutcome

/-- Untyped merge sort has linearithmic worst-case cost. -/
theorem merge_sort_untyped.«BigO(n * (Nat.log2 n + 1), n = len(values))» :
    CleanXY.Property.Function.BigO
      SortAst.module "merge_sort_untyped" (.listLength "values")
        (fun n => n * (Nat.log2 n + 1)) := by
  apply CleanXY.Property.Function.bigO_of_growth_bound
    (inputSize := .listLength "values") (growth := .linearithmic)
  · rfl
  · rfl
  · exact CleanXY.PyAst.Growth.linearithmic_isBigO

/-- Untyped first-element-pivot quicksort has quadratic worst-case cost. -/
theorem quick_sort.«BigO(n * n, n = len(values))» :
    CleanXY.Property.Function.BigO
      SortAst.module "quick_sort" (.listLength "values") (fun n => n * n) := by
  apply CleanXY.Property.Function.bigO_of_growth_bound
    (inputSize := .listLength "values") (growth := .quadratic)
  · rfl
  · rfl
  · exact CleanXY.PyAst.Growth.quadratic_isBigO

end tests.py.sort
