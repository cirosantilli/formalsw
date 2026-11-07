import lang.py.FormalSW.HeapRuntimeCostRecords
import lang.py.FormalSW.HeapRuntimeCostListCopies

namespace FormalSW.PyAst.HeapCalls.Runtime

/-- The receiver is retained separately from the explicit method arguments. -/
def MethodReturnsIn (arithmetic : PrimitiveWork.Arithmetic) (module : Module)
    (receiver : Value) (args : List Arg) (body : List Stmt) (values : List Value)
    (heap : Heap) (budget : Nat) (value : Value) (finalHeap : Heap) : Prop :=
  ∀ anchors stack, Reaches arithmetic module anchors
    ⟨.operation (.method receiver args body) values, stack, heap⟩ budget
    ⟨.value value, stack, finalHeap⟩

theorem MethodReturnsIn.of_body
    (arguments : completeArguments args (receiver :: values) = some completed)
    (execution : BlockReturnsIn arithmetic module (functionEnv args body completed []) (executableBody body)
      heap budget value finalHeap) :
    MethodReturnsIn arithmetic module receiver args body values heap (values.length+args.length+2+budget)
      value finalHeap := by
  intro anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.operation (.method receiver args body) values, stack, heap⟩ (values.length+args.length+2)
      ⟨.block (executableBody body) (functionEnv args body completed []), stack, heap⟩ :=
    advance (by simp [step, invokeMethod, arguments])
      (by simp [charge, operation, Nat.add_assoc]) rfl
  exact first.trans (execution anchors stack)

/-- Binding precedes evaluation of the arguments, which may mutate the receiver. -/
theorem EvaluatesIn.method {field : String}
    (lookup : env name = some receiver) (ordinary : field ≠ "append" ∧ field ≠ "add")
    (bound : bindMethod module receiver field heap = some (.ok (.method receiver args body), heap))
    (priced : RecordWork.method module heap receiver field = some work)
    (arguments : ArgumentsIn arithmetic module env 0 expressions heap ca values middle)
    (execution : MethodReturnsIn arithmetic module receiver args body values middle cb value finalHeap) :
    EvaluatesIn arithmetic module env (.call (.attribute (.name name) field) expressions) heap
      (ca+cb+work+3) value finalHeap := by
  intro anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.expr (.call (.attribute (.name name) field) expressions) env, stack, heap⟩ 1
      ⟨.expr (.name name) env, .methodReceiver field expressions env :: stack, heap⟩ :=
    advance (by simp [step, ordinary.1, ordinary.2, lookup])
      (by simp [charge]) rfl
  have loaded := EvaluatesIn.lookup (arithmetic := arithmetic) (module := module) (heap := heap)
    lookup anchors (.methodReceiver field expressions env :: stack)
  have boundRun : Reaches arithmetic module anchors
      ⟨.value receiver, .methodReceiver field expressions env :: stack, heap⟩ (work+1)
      (argumentsState (.method receiver args body) env [] expressions stack heap) :=
    advance (by simp [step, run, bound]) (by simp [charge, priced])
      (by cases expressions <;> rfl)
  exact ((((first.trans loaded).trans boundRun).trans
    (arguments.reaches (.method receiver args body) anchors stack)).trans (execution anchors stack)).mono (by omega)

/-- A Python initializer must finish with None before the fresh instance is returned. -/
theorem ReturnsIn.constructor
    (noFunction : findFunctionIn module.body name = none)
    (noLibrary : libraryFunction module name = none)
    (defined : module.findClass name = some (origin, classBody))
    (initializer : findFunctionIn classBody "__init__" = some (args, body))
    (arguments : completeArguments args (.ref heap.length :: values) = some completed)
    (execution : BlockReturnsIn arithmetic module (functionEnv args body completed []) (executableBody body)
      (heap ++ [.instance origin name []]) budget (.scalar .none) finalHeap) :
    ReturnsIn arithmetic module name values heap (budget+values.length+args.length+4)
      (.ref heap.length) finalHeap := by
  intro anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.operation (.call name) values, stack, heap⟩ (values.length+args.length+3)
      ⟨.block (executableBody body) (functionEnv args body completed []),
        .initialized heap.length :: stack, heap ++ [.instance origin name []]⟩ := by
    apply RuntimeCost.Amortized.Reaches.next (amount := values.length+args.length+3)
    · simp [step, noFunction, noLibrary, construct, defined, initializer, invokeMethod, arguments]
    · simp [charge, noFunction, noLibrary, RecordWork.construct, defined, initializer, Nat.add_assoc]
    · simp [potential, heapPotential, objectPotential]
  have last : Reaches arithmetic module anchors
      ⟨.value (.scalar .none), .initialized heap.length :: stack, finalHeap⟩ 1
      ⟨.value (.ref heap.length), stack, finalHeap⟩ := advance rfl rfl rfl
  exact ((first.trans (execution anchors _)).trans last).mono (by omega)

theorem BlockReturnsIn.fallthrough :
    BlockReturnsIn arithmetic module env [] heap 1 (.scalar .none) heap :=
  fun _ _ => advance rfl rfl rfl

private theorem assigned_field
    (target : EvaluatesIn arithmetic module env base afterRhs ct receiver afterTarget)
    (write : Mutable.writeField receiver name value afterTarget = some (.ok (.scalar .none), afterWrite))
    (priced : RecordWork.write afterTarget receiver name = some work)
    (credits : heapPotential afterWrite = heapPotential afterTarget) :
    Reaches arithmetic module anchors
      ⟨.value value, .assignAttribute base name following env :: stack, afterRhs⟩ (ct+work+4)
      ⟨.block following env, stack, afterWrite⟩ := by
  have first : Reaches arithmetic module anchors
      ⟨.value value, .assignAttribute base name following env :: stack, afterRhs⟩ 1
      (argumentsState (.setField name value) env [] [base] (.discard following env :: stack) afterRhs) :=
    advance rfl rfl rfl
  have args := (ArgumentsIn.cons target ArgumentsIn.nil).reaches (completed := []) (.setField name value) anchors
    (.discard following env :: stack)
  have written : Reaches arithmetic module anchors
      ⟨.operation (.setField name value) [receiver], .discard following env :: stack, afterTarget⟩ (work+1)
      ⟨.value (.scalar .none), .discard following env :: stack, afterWrite⟩ := by
    apply RuntimeCost.Amortized.Reaches.next (amount := work+1)
    · simp [step, result, run, primitive, write]
    · simp [charge, operation, priced]
    · simp [potential, credits]
  have last : Reaches arithmetic module anchors
      ⟨.value (.scalar .none), .discard following env :: stack, afterWrite⟩ 1
      ⟨.block following env, stack, afterWrite⟩ := advance rfl rfl rfl
  exact (((first.trans args).trans written).trans last).mono (by simp only [List.length_nil]; omega)

/-- The RHS is evaluated before the destination instance is read. -/
theorem BlockContinuesIn.setAttribute
    (rhs : EvaluatesIn arithmetic module env expression heap cr value afterRhs)
    (target : EvaluatesIn arithmetic module env base afterRhs ct receiver afterTarget)
    (write : Mutable.writeField receiver name value afterTarget = some (.ok (.scalar .none), afterWrite))
    (priced : RecordWork.write afterTarget receiver name = some work)
    (credits : heapPotential afterWrite = heapPotential afterTarget) :
    BlockContinuesIn arithmetic module env [.assign [.attribute base name] expression] heap
      (cr+ct+work+5) env afterWrite := by
  intro following anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.block ([.assign [.attribute base name] expression] ++ following) env, stack, heap⟩ 1
      ⟨.expr expression env, .assignAttribute base name following env :: stack, heap⟩ := advance rfl rfl rfl
  exact ((first.trans (rhs anchors _)).trans (assigned_field target write priced credits)).mono (by omega)

/-- Local annotations do not run when assigning a field. -/
theorem BlockContinuesIn.annAttribute
    (rhs : EvaluatesIn arithmetic module env expression heap cr value afterRhs)
    (target : EvaluatesIn arithmetic module env base afterRhs ct receiver afterTarget)
    (write : Mutable.writeField receiver name value afterTarget = some (.ok (.scalar .none), afterWrite))
    (priced : RecordWork.write afterTarget receiver name = some work)
    (credits : heapPotential afterWrite = heapPotential afterTarget) :
    BlockContinuesIn arithmetic module env [.annAssign (.attribute base name) annotation (some expression)] heap
      (cr+ct+work+5) env afterWrite := by
  intro following anchors stack
  have first : Reaches arithmetic module anchors
      ⟨.block ([.annAssign (.attribute base name) annotation (some expression)] ++ following) env, stack, heap⟩ 1
      ⟨.expr expression env, .assignAttribute base name following env :: stack, heap⟩ := advance rfl rfl rfl
  exact ((first.trans (rhs anchors _)).trans (assigned_field target write priced credits)).mono (by omega)

end FormalSW.PyAst.HeapCalls.Runtime
