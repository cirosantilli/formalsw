import «.cleanxy».tests.«sort.py.ast»
import CleanXY

namespace tests.sort

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

end tests.sort
