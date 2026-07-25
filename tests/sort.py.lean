import «.cleanxy».tests.«sort.py.ast»
import CleanXY

namespace tests.sort

/-- Mixed values expose the algorithms' different comparison behavior. -/
theorem merge_sort.«Not Equiv(quick_sort)» :
    Not (CleanXY.Property.Function.Equiv
      SortAst.module "merge_sort" "quick_sort") := by
  intro equivalent
  obtain ⟨outcome, mergeOutcome, quickOutcome⟩ :=
    equivalent [.int 0, .string ""]
  change some (.error {
    typeName := "TypeError"
    args := [.string "'<=' not supported between instances of 'int' and 'str'"]
  }) = some outcome at mergeOutcome
  change some (.error {
    typeName := "TypeError"
    args := [.string "'<' not supported between instances of 'str' and 'int'"]
  }) = some outcome at quickOutcome
  injection mergeOutcome with mergeOutcome
  injection quickOutcome with quickOutcome
  rw [← mergeOutcome] at quickOutcome
  simp at quickOutcome

/-- Merge sort has linearithmic worst-case cost. -/
theorem merge_sort.«BigO(n * (Nat.log2 n + 1), n = len(values))» :
    CleanXY.Property.Function.BigO
      SortAst.module "merge_sort" (.listLength "values")
        (fun n => n * (Nat.log2 n + 1)) := by
  apply CleanXY.Property.Function.bigO_of_growth_bound
    (inputSize := .listLength "values") (growth := .linearithmic)
  · rfl
  · rfl
  · exact CleanXY.PyAst.Growth.linearithmic_isBigO

/-- This first-element-pivot quicksort has quadratic worst-case cost. -/
theorem quick_sort.«BigO(n * n, n = len(values))» :
    CleanXY.Property.Function.BigO
      SortAst.module "quick_sort" (.listLength "values") (fun n => n * n) := by
  apply CleanXY.Property.Function.bigO_of_growth_bound
    (inputSize := .listLength "values") (growth := .quadratic)
  · rfl
  · rfl
  · exact CleanXY.PyAst.Growth.quadratic_isBigO

end tests.sort
