import lang.py.FormalSW.MachineExpressionInvariant

/-! Exception exits retain shared memory, suspended references, and generator boundaries. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

/-- The exception observation boundary accepts scalar payloads only. -/
def exceptionArguments : List Value → Option (List Constant)
  | [] => some []
  | .scalar value :: rest => (exceptionArguments rest).map (value :: ·)
  | .ref _ :: _ => none

theorem exceptionArguments_relocates (rename : Nat → Nat) (values : List Value) :
    exceptionArguments (values.map (relocateValue rename)) = exceptionArguments values := by
  induction values with
  | nil => rfl
  | cons value rest ih => cases value <;> simp [exceptionArguments, relocateValue, ih]

theorem exceptionArguments_eval (values : List Value) (heap : Mutable.Heap) :
    (values.mapM (fun value => match value with
      | .scalar scalar => pure scalar
      | .ref _ => Mutable.unsupported) : Mutable.Eval (List Constant)) heap =
      (exceptionArguments values).map (fun args => (.ok args, heap)) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    cases value with
    | ref address => simp [List.mapM_cons, exceptionArguments, Mutable.eval_bind, Mutable.unsupported]
    | scalar scalar =>
      simp only [List.mapM_cons, Mutable.eval_bind, Mutable.eval_pure]
      dsimp only [bind, Option.bind]
      rw [ih]
      simp only [exceptionArguments]
      cases exceptionArguments rest <;> rfl

theorem raiseException_result (typeName : String) (values : List Value) (heap : Mutable.Heap) :
    primitive (.raiseException typeName) values heap =
      (exceptionArguments values).map (fun args => (.error {typeName, args}, heap)) := by
  change ((do
    let args ← values.mapM (fun value => match value with
      | .scalar scalar => pure scalar
      | .ref _ => Mutable.unsupported)
    throw {typeName, args}) : Mutable.Eval Value) heap = _
  simp only [Mutable.eval_bind, exceptionArguments_eval]
  cases exceptionArguments values <;> rfl

theorem step_raiseException_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (typeName : String) (values : List Value)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.raiseException typeName) values, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.operation (.raiseException typeName) values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have raw := result_readonly_preserves logical physical rename logicalAnchors physicalAnchors
    (primitive (.raiseException typeName) values)
    (primitive (.raiseException typeName) (values.map (relocateValue rename))) stack globals layout stackInside globalsInside (by
      intro outcome after executed
      rw [raiseException_result] at executed
      cases decoded : exceptionArguments values with
      | none => simp [decoded] at executed
      | some args =>
        simp only [decoded, Option.map_some, Option.some.injEq, Prod.mk.injEq] at executed
        refine ⟨executed.2.symm, ?_⟩
        intro value success
        rw [← executed.1] at success
        cases success) (by
      simp only [raiseException_result, exceptionArguments_relocates]
      cases exceptionArguments values <;> rfl)
  exact raw.protectGenerator stack stackInside

theorem step_raise_call_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (typeName : String) (arguments : List Expr)
    (following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.block (.raise (some (.call (.name typeName) arguments)) :: following) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.raise (some (.call (.name typeName) arguments)) :: following) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.block (.raise (some (.call (.name typeName) arguments)) :: following) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · exact argumentsState_heap ..
  · exact argumentsState_within logical (.raiseException typeName) env [] arguments stack
      (by simp [OperationWithin]) inside.1.1 (by simp) inside.2
  · simpa only [step, relocateState, relocateWork, List.map_cons, relocateStmt, protectGenerator_next,
      relocateStep] using congrArg Step.next (argumentsState_relocates rename logical physical
        (.raiseException typeName) env [] arguments stack)

theorem step_raise_name_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (typeName : String) (following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.block (.raise (some (.name typeName)) :: following) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.raise (some (.name typeName)) :: following) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.block (.raise (some (.name typeName)) :: following) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · rfl
  · exact ⟨⟨by simp [OperationWithin], by simp⟩, inside.2⟩
  · simp [step, relocateState, relocateWork, relocateStmt, relocateStep, argumentsState,
      relocateRuntimeOperation, relocateOperation]

theorem step_assert_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (condition : Expr) (message : Option Expr)
    (following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.block (.assert condition message :: following) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.assert condition message :: following) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.block (.assert condition message :: following) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · rfl
  · refine ⟨inside.1.1, ?_⟩
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simp only [FrameWithin]
      exact ⟨inside.1.1, fun statement member => inside.1.2 statement (List.mem_cons_of_mem _ member)⟩
    · exact inside.2 frame member
  · simp only [step, relocateState, relocateWork, List.map_cons, relocateStmt, relocateFrame,
      protectGenerator_next, relocateStep]

theorem step_assertion_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (message : Option Expr)
    (following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .assertion message following env :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .assertion message following env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .assertion message following env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have saved := inside.2 _ (List.mem_cons_self ..)
  simp only [FrameWithin] at saved
  have stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame :=
    fun frame member => inside.2 frame (List.mem_cons_of_mem _ member)
  obtain ⟨truth, tested⟩ := truth_total logical value inside.1
  have paired := layout.runtime.truth value inside.1
  apply Preserves.unchanged layout
  · apply protectGenerator_heap
    cases truth <;> cases message <;> simp [run, tested, done, StepHeap]
  · apply protectGenerator_within
    cases truth with
    | true =>
      simp only [run, tested, if_true, StepWithin]
      exact ⟨⟨saved.1, saved.2⟩, stackInside⟩
    | false =>
      cases message with
      | none =>
        simp only [run, tested, Bool.false_eq_true, if_false, done, StepWithin]
        exact ⟨globalsInside, by intro value impossible; cases impossible⟩
      | some expression =>
        simp only [run, tested, Bool.false_eq_true, if_false, StepWithin]
        refine ⟨saved.1, ?_⟩
        intro frame member
        rcases List.mem_cons.mp member with rfl | member
        · simp [FrameWithin]
        · exact stackInside frame member
  · cases truth <;> cases message <;>
      simp [step, run, tested, paired, done, relocateStep, relocateState, relocateWork, relocateCompletion,
        relocateFrame, protectGenerator, Calls.generatorException, Except.map]

theorem step_assertionMessage_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .assertionMessage :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .assertionMessage :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · apply protectGenerator_heap
    cases value with
    | scalar scalar => rfl
    | ref address => trivial
  · apply protectGenerator_within
    cases value with
    | scalar scalar => exact ⟨globalsInside, by intro value impossible; cases impossible⟩
    | ref address => trivial
  · cases value <;>
      simp [step, done, relocateStep, relocateState, relocateWork, relocateCompletion,
        relocateFrame, relocateValue, protectGenerator, Calls.generatorException, Except.map]

theorem exceptionArguments_scalars (values : List Constant) :
    exceptionArguments (values.map Mutable.Value.scalar) = some values := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [exceptionArguments, ih]

/-- Explicit payloads survive ordinary raises; generator boundaries translate StopIteration. -/
theorem step_raise_scalars (module : Module) (heap : Mutable.Heap) (anchors : Nat)
    (typeName : String) (values : List Constant) (stack : List Frame) (globals : Mutable.Globals) :
    step module anchors ⟨.operation (.raiseException typeName) (values.map Mutable.Value.scalar), stack, heap⟩ globals =
      .done (.ok ⟨.error (Calls.generatorException (stack.any Frame.inGenerator) ⟨typeName, values⟩),
        globals, heap, anchors⟩) := by
  simp [step, result, run, raiseException_result, exceptionArguments_scalars, done, protectGenerator]

end FormalSW.PyAst.HeapCalls.Relocation

