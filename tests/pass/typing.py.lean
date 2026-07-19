import «.cleanxyz».tests.pass.«typing.py.ast»
import CleanXYZ

namespace tests.pass.typing

/-- An unrestricted comparison can receive incompatible runtime types. -/
theorem merge_sort_untyped.«Throws» :
    CleanXYZ.Property.Function.Throws TypingAst.module "merge_sort_untyped" := by
  refine ⟨.int 0, .string "", { typeName := "TypeError", args := [] }, ?_⟩
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- Two integer arguments are always mutually comparable. -/
theorem merge_sort_int.«Not Throws» :
    Not (CleanXYZ.Property.Function.Throws TypingAst.module "merge_sort_int") := by
  rintro ⟨left, right, exception, hleft, hright, houtcome⟩
  cases left <;> cases right <;> simp [
    CleanXYZ.PyAst.evalBinaryComparisonOutcome,
    CleanXYZ.PyAst.Module.findBinaryComparison,
    CleanXYZ.PyAst.findBinaryComparisonIn,
    CleanXYZ.PyAst.executableBody,
    CleanXYZ.PyAst.scalarKindFromAnnotation,
    CleanXYZ.PyAst.ScalarKind.accepts,
    TypingAst.module,
  ] at hleft hright houtcome

/-- Two string arguments are always mutually comparable. -/
theorem merge_sort_str.«Not Throws» :
    Not (CleanXYZ.Property.Function.Throws TypingAst.module "merge_sort_str") := by
  rintro ⟨left, right, exception, hleft, hright, houtcome⟩
  cases left <;> cases right <;> simp [
    CleanXYZ.PyAst.evalBinaryComparisonOutcome,
    CleanXYZ.PyAst.Module.findBinaryComparison,
    CleanXYZ.PyAst.findBinaryComparisonIn,
    CleanXYZ.PyAst.executableBody,
    CleanXYZ.PyAst.scalarKindFromAnnotation,
    CleanXYZ.PyAst.ScalarKind.accepts,
    TypingAst.module,
  ] at hleft hright houtcome

end tests.pass.typing
