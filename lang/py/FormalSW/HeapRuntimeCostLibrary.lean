import lang.py.FormalSW.HeapRuntimeCostControl

namespace FormalSW.PyAst.HeapCalls.Runtime

@[simp] theorem scalarValues_map (values : List Constant) :
    scalarValues (values.map Mutable.Value.scalar) = some values := by
  simp [scalarValues, List.mapM_map, Function.comp_def]
  induction values with
  | nil => rfl
  | cons value values ih => simp [List.mapM_cons, ih]

/-- A scalar library call pays its declared tariff and preserves the heap. -/
theorem ReturnsIn.library
    (notLocal : findFunctionIn module.body name = none)
    (imported : libraryFunction module name = some implementation)
    (evaluated : HeapCalls.library module name (values.map Mutable.Value.scalar) heap = some (.ok answer, heap))
    (priced : Calls.Runtime.library arithmetic module name values = some work) :
    ReturnsIn arithmetic module name (values.map Mutable.Value.scalar) heap (work+1) answer heap := by
  intro anchors stack
  apply advance
  · simp [step, notLocal, imported, result, run, evaluated]
  · simp [charge, notLocal, priced]
  · rfl

end FormalSW.PyAst.HeapCalls.Runtime
