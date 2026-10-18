import lang.py.FormalSW.HeapCalls

/-! Compositional proofs for plain Python constructors, methods, and fields. -/
namespace FormalSW.PyAst.HeapCalls

variable {globals : Mutable.Globals}


/-- A bound method retains its original definition even if its field is rebound. -/
def MethodReturns (module : Module) (receiver : Value) (args : List Arg) (body : List Stmt)
    (values : List Value) (heap : Heap) (value : Value) (finalHeap : Heap) (globals : Mutable.Globals := []) : Prop :=
  ∀ anchors stack, Reaches (globals := globals) module anchors
    ⟨.operation (.method receiver args body) values, stack, heap⟩
    ⟨.value value, stack, finalHeap⟩

theorem MethodReturns.of_body
    (arguments : completeArguments args (receiver :: values) = some completed)
    (execution : BlockReturns (globals := globals) module (functionEnv args body completed globals) (executableBody body) heap value finalHeap) :
    MethodReturns (globals := globals) module receiver args body values heap value finalHeap := by
  intro anchors stack
  exact .next (by simp [step, invokeMethod, arguments]) (execution anchors stack)

theorem MethodReturns.extend (result : MethodReturns (globals := globals) source receiver args body values heap value finalHeap)
    (extension : Extends target source) : MethodReturns (globals := globals) target receiver args body values heap value finalHeap :=
  fun anchors stack => (result anchors stack).extend extension

theorem Evaluates.field
    (receiver : Evaluates (globals := globals) module env base heap object middle)
    (read : getAttribute module object name middle = some (.ok value, finalHeap)) :
    Evaluates (globals := globals) module env (.attribute base name) heap value finalHeap := by
  intro anchors stack
  exact .next rfl ((receiver anchors _).trans
    (.next (by simp [step, result, run, read]) .refl))

/-- Bind a local receiver before evaluating any method arguments. -/
theorem Evaluates.method {field : String}
    (lookup : env name = some receiver)
    (ordinary : field ≠ "append" ∧ field ≠ "add")
    (bound : bindMethod module receiver field heap = some (.ok (.method receiver args body), heap))
    (arguments : Evaluates.Arguments (globals := globals) module env expressions heap values middle)
    (execution : MethodReturns (globals := globals) module receiver args body values middle value finalHeap) :
    Evaluates (globals := globals) module env (.call (.attribute (.name name) field) expressions) heap value finalHeap := by
  intro anchors stack
  apply Reaches.next (following := ⟨.expr (.name name) env, .methodReceiver field expressions env :: stack, heap⟩)
    (by simp [step, ordinary.1, ordinary.2, lookup])
  apply Reaches.next (following := ⟨.value receiver, .methodReceiver field expressions env :: stack, heap⟩)
    (by simp [step, lookup])
  apply Reaches.next (following := argumentsState (.method receiver args body) env [] expressions stack heap)
    (by simp [step, run, bound])
  exact (Evaluates.arguments_reach arguments (.method receiver args body) [] anchors stack).trans
    (execution anchors stack)

/-- The initializer writes into a fresh instance and must return None. -/
theorem ReturnsValue.constructor
    (noFunction : findFunctionIn module.body name = none)
    (noLibrary : libraryFunction module name = none)
    (defined : module.findClass name = some (origin, classBody))
    (initializer : findFunctionIn classBody "__init__" = some (args, body))
    (arguments : completeArguments args (.ref heap.length :: values) = some completed)
    (execution : BlockReturns (globals := globals) module (functionEnv args body completed globals) (executableBody body)
      (heap ++ [.instance origin name []]) (.scalar .none) finalHeap) :
    ReturnsValue (globals := globals) module name values heap (.ref heap.length) finalHeap := by
  intro anchors stack
  apply Reaches.next (following := ⟨.block (executableBody body) (functionEnv args body completed globals),
    .initialized heap.length :: stack, heap ++ [.instance origin name []]⟩)
    (by simp [step, noFunction, noLibrary, construct, defined, initializer, invokeMethod, arguments])
  exact (execution anchors _).trans (.next rfl .refl)

theorem ReturnsValue.empty_constructor
    (noFunction : findFunctionIn module.body name = none)
    (noLibrary : libraryFunction module name = none)
    (defined : module.findClass name = some (origin, classBody))
    (initializer : findFunctionIn classBody "__init__" = none) :
    ReturnsValue (globals := globals) module name [] heap (.ref heap.length) (heap ++ [.instance origin name []]) := by
  intro anchors stack
  exact .next (by simp [step, noFunction, noLibrary, construct, defined, initializer,
    result, run, Mutable.allocateInstance_result]) .refl

private theorem assigned_field
    (target : Evaluates (globals := globals) module env base afterRhs receiver afterTarget)
    (write : Mutable.writeField receiver name value afterTarget = some (.ok (.scalar .none), afterWrite)) :
    Reaches (globals := globals) module anchors ⟨.value value, .assignAttribute base name following env :: stack, afterRhs⟩
      ⟨.block following env, stack, afterWrite⟩ := by
  apply Reaches.next rfl
  apply (Evaluates.arguments_reach (.cons target .nil) (.setField name value) [] anchors _).trans
  exact .next (following := ⟨.value (.scalar .none), .discard following env :: stack, afterWrite⟩)
    (by simp [step, result, run, primitive, write]) (.next rfl .refl)

/-- Assignment evaluates its RHS before looking up the destination instance. -/
theorem BlockContinues.setAttribute
    (rhs : Evaluates (globals := globals) module env expression heap value afterRhs)
    (target : Evaluates (globals := globals) module env base afterRhs receiver afterTarget)
    (write : Mutable.writeField receiver name value afterTarget = some (.ok (.scalar .none), afterWrite)) :
    BlockContinues (globals := globals) module env [.assign [.attribute base name] expression] heap env afterWrite := by
  intro following anchors stack
  exact .next rfl ((rhs anchors _).trans (assigned_field target write))

theorem BlockContinues.annAttribute {annotation : Expr}
    (rhs : Evaluates (globals := globals) module env expression heap value afterRhs)
    (target : Evaluates (globals := globals) module env base afterRhs receiver afterTarget)
    (write : Mutable.writeField receiver name value afterTarget = some (.ok (.scalar .none), afterWrite)) :
    BlockContinues (globals := globals) module env [.annAssign (.attribute base name) annotation (some expression)] heap env afterWrite := by
  intro following anchors stack
  exact .next rfl ((rhs anchors _).trans (assigned_field target write))

end FormalSW.PyAst.HeapCalls
