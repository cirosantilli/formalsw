import «.cleanxyz».tests.pass.«sort.py.ast»
import CleanXYZ

namespace tests.pass.sort

/-- The two recognized sorting implementations have the same result. -/
theorem merge_sort.«Equiv(quick_sort)» :
    CleanXYZ.Property.Function.Equiv
      SortAst.module "merge_sort" "quick_sort" := by
  intro values
  refine ⟨CleanXYZ.PyAst.canonicalSort values, ?_⟩
  constructor <;> rfl

/-- Merge sort has linearithmic worst-case cost. -/
theorem merge_sort.«BigO(n * (Nat.log2 n + 1), n = len(values))» :
    CleanXYZ.Property.Function.BigO
      SortAst.module "merge_sort" (.listLength "values")
        (fun n => n * (Nat.log2 n + 1)) := by
  apply CleanXYZ.Property.Function.bigO_of_growth_bound
    (inputSize := .listLength "values") (growth := .linearithmic)
  · rfl
  · rfl
  · exact CleanXYZ.PyAst.Growth.linearithmic_isBigO

/-- This first-element-pivot quicksort has quadratic worst-case cost. -/
theorem quick_sort.«BigO(n * n, n = len(values))» :
    CleanXYZ.Property.Function.BigO
      SortAst.module "quick_sort" (.listLength "values") (fun n => n * n) := by
  apply CleanXYZ.Property.Function.bigO_of_growth_bound
    (inputSize := .listLength "values") (growth := .quadratic)
  · rfl
  · rfl
  · exact CleanXYZ.PyAst.Growth.quadratic_isBigO

end tests.pass.sort
