import lang.py.FormalSW.HeapRuntimeCostControl

namespace FormalSW.PyAst.HeapCalls.Runtime

/-- Stored-field access pays for name lookup, retaining the value reference. -/
theorem EvaluatesIn.field
    (receiver : EvaluatesIn arithmetic module env base heap budget object middle)
    (read : getAttribute module object name middle = some (.ok value, middle))
    (priced : RecordWork.field middle object name = some work) :
    EvaluatesIn arithmetic module env (.attribute base name) heap (budget+work+2) value middle := by
  intro anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.expr (.attribute base name) env, stack, heap⟩ 1
      ⟨.expr base env, .attribute name :: stack, heap⟩ := advance rfl rfl rfl
  have last : Reaches arithmetic module anchors
      ⟨.value object, .attribute name :: stack, middle⟩ (work+1)
      ⟨.value value, stack, middle⟩ :=
    advance (by simp [step, result, run, read]) (by simp [charge, priced]) rfl
  exact ((first.trans (receiver anchors _)).trans last).mono (by omega)

/-- A generated dataclass initializer copies its positional field references. -/
theorem ReturnsIn.dataclass_constructor
    (noFunction : findFunctionIn module.body name = none)
    (noLibrary : libraryFunction module name = none)
    (defined : module.findClass name = some (origin, classBody))
    (initializer : findFunctionIn classBody "__init__" = none)
    (metadata : dataclassFields classBody = some (frozen, fields))
    (arity : fields.length = values.length) :
    ReturnsIn arithmetic module name values heap (fields.length+values.length+2) (.ref heap.length)
      (heap ++ [.dataInstance origin name frozen (fields.map Arg.name) ((fields.map Arg.name).zip values)]) := by
  intro anchors stack
  apply RuntimeCost.Amortized.Reaches.next (amount := fields.length+values.length+2)
  · simp [step, noFunction, noLibrary, construct, defined, initializer, metadata, result, run,
      Mutable.allocateDataclass_result origin name frozen (fields.map Arg.name) values heap (by simpa using arity)]
  · simp [charge, noFunction, noLibrary, RecordWork.construct, defined, initializer,
      metadata, arity, Nat.add_assoc]
  · simp [potential, heapPotential, objectPotential]

end FormalSW.PyAst.HeapCalls.Runtime
