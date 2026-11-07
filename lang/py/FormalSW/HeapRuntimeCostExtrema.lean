import lang.py.FormalSW.HeapRuntimeCostPrimitives

namespace FormalSW.PyAst.HeapCalls.Runtime

/-- The maximum library call scans scalar list contents. Pointer copying does
not justify a bound for arbitrary object comparison callbacks. -/
theorem EvaluatesIn.list_maximum
    (argument : EvaluatesIn arithmetic module env expression heap ca (.ref address) middle)
    (found : middle[address]? = some (.list (items.map Mutable.Value.scalar)))
    (evaluated : ScalarSet.maximum items = .ok answer) :
    EvaluatesIn arithmetic module env (.builtinCall .max [expression]) heap
      (ca+SetWork.extremum arithmetic items+3) (.scalar answer) middle := by
  apply EvaluatesIn.builtin_single (by intro h; cases h) (by intro h; cases h) argument
  · have readScalars : (items.mapM (fun value => pure value) : Mutable.Eval (List Constant)) = pure items := by
      simpa using (List.mapM_pure (m := Mutable.Eval) (l := items) (f := id))
    simp [primitive, Mutable.sequence, found, List.mapM_map, Function.comp_def, readScalars, scalarResult, evaluated]
  · have scalars : items.mapM (fun value => some value) = some items := by
      simpa using (List.mapM_pure (m := Option) (l := items) (f := id))
    simp [operation, found, scalarValues, List.mapM_map, Function.comp_def, scalars]

end FormalSW.PyAst.HeapCalls.Runtime
