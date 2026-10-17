import «.cleanxy».tests.py.«sort.py.ast»
import CleanXY

namespace tests.py.sort

open CleanXY.PyAst

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
  apply Execution.finishes_of_observe (fuel := 20)
  native_decide

/-- Every comparison actually used by merge sort must finish successfully.
The comparison may execute a user-defined method with loops. -/
theorem merge_sort_untyped.returns_of_le_safe (values : List Value) :
    let _this_module := SortAst.module
    let this_function := listFunction _this_module "merge_sort_untyped"
    (∀ left ∈ values, ∀ right ∈ values, Returns(left <= right)) →
    Returns(this_function(values)) := by
  dsimp only
  intro safe
  have recognized : isMergeSortFunction SortAst.module "merge_sort_untyped" = true := by native_decide
  rw [listFunction, recognized]
  obtain ⟨result, finished, _⟩ := mergeSortExecution_returns
    (comparison SortAst.module .ltE) values safe
  exact ⟨result, finished⟩

/-- Successful custom comparisons execute the actual method body too. -/
example (a b : Int) :
    (comparison SortAst.module .ltE (.object "DummyInt" (some a)) (.object "DummyInt" (some b))).Returns := by
  refine ⟨decide (a ≤ b), Execution.finishes_bind_ok (value := .bool (decide (a ≤ b))) (.done ?_) (.done rfl)⟩
  rfl

/-- An empty object does not acquire a synthetic integer field. -/
example : (comparison SortAst.module .ltE
    (.object "DummyInt") (.object "DummyInt")).observe 5 = .unsupported := by native_decide

/-- The execution returns the actual merged list, without canonical normalization. -/
example : (listFunction SortAst.module "merge_sort_untyped"
    [.object "DummyInt" (some 2), .object "DummyInt" (some 1)]).observe 30 =
      .done (.ok [.object "DummyInt" (some 1), .object "DummyInt" (some 2)]) := by native_decide

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

private def loopingComparison : Stmt :=
  .whileDo (.constant (.bool true)) [.expr (.constant .none)] []

private theorem looping_block_diverges (env : ScalarEnv) :
    (scalarBlock [loopingComparison] env).Diverges := by
  refine ⟨fun state => state.todo = [loopingComparison] ∨
    state.todo = [.expr (.constant .none), loopingComparison], Or.inl rfl, ?_⟩
  rintro ⟨todo, env⟩ (h | h)
  · simp only at h
    subst todo
    exact ⟨⟨[.expr (.constant .none), loopingComparison], env⟩, rfl, Or.inr rfl⟩
  · simp only at h
    subst todo
    exact ⟨⟨[loopingComparison], env⟩, rfl, Or.inl rfl⟩

/-- Sorting waits forever for this object's actual __le__ method. -/
theorem merge_sort_untyped.loops_on_bad_comparison :
    let this_function := listFunction SortAst.module "merge_sort_untyped"
    Not Halts(this_function([.object "Looping", .object "Looping"])) := by
  dsimp only
  have recognized : isMergeSortFunction SortAst.module "merge_sort_untyped" = true := by native_decide
  rw [listFunction, recognized]
  apply mergeSort_pair_not_halts
  intro halted
  have body_halts := Execution.halts_of_bind halted
  exact Execution.diverges_not_halts (looping_block_diverges _) body_halts

end tests.py.sort
