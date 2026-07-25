import «.cleanxy».tests.«typing.py.ast»
import CleanXY

namespace tests.typing

/-- An unrestricted comparison can receive incompatible runtime types. -/
theorem merge_sort_untyped.«Throws» :
    CleanXY.Property.Function.Throws TypingAst.module "merge_sort_untyped" := by
  refine ⟨.int 0, .string [], { typeName := "TypeError", args := [] }, ?_⟩
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- Two integer arguments are always mutually comparable. -/
theorem merge_sort_int.«Not Throws» :
    Not (CleanXY.Property.Function.Throws TypingAst.module "merge_sort_int") := by
  rintro ⟨left, right, exception, hleft, hright, houtcome⟩
  cases left <;> cases right <;> simp [
    CleanXY.PyAst.evalBinaryComparisonOutcome,
    CleanXY.PyAst.Module.findBinaryComparison,
    CleanXY.PyAst.findBinaryComparisonIn,
    CleanXY.PyAst.executableBody,
    CleanXY.PyAst.scalarKindFromAnnotation,
    CleanXY.PyAst.ScalarKind.accepts,
    TypingAst.module,
  ] at hleft hright houtcome

/-- Two string arguments are always mutually comparable. -/
theorem merge_sort_str.«Not Throws» :
    Not (CleanXY.Property.Function.Throws TypingAst.module "merge_sort_str") := by
  rintro ⟨left, right, exception, hleft, hright, houtcome⟩
  cases left <;> cases right <;> simp [
    CleanXY.PyAst.evalBinaryComparisonOutcome,
    CleanXY.PyAst.Module.findBinaryComparison,
    CleanXY.PyAst.findBinaryComparisonIn,
    CleanXY.PyAst.executableBody,
    CleanXY.PyAst.scalarKindFromAnnotation,
    CleanXY.PyAst.ScalarKind.accepts,
    TypingAst.module,
  ] at hleft hright houtcome

end tests.typing
