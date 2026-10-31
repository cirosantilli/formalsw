import lang.py.FormalSW.MachineMethodInvariant
import lang.py.FormalSW.ClassCalls

/-! Call dispatch retains evaluation order and saved caller references. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem step_attribute_call (module : Module) (heap : Mutable.Heap) (anchors : Nat)
    (base : Expr) (field : String) (expressions : List Expr) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) :
    step module anchors ⟨.expr (.call (.attribute base field) expressions) env, stack, heap⟩ globals =
      match field, expressions with
      | "append", [item] => .next ⟨.expr base env, .appendReceiver item env :: stack, heap⟩
      | "add", [item] => .next ⟨.expr base env, .addReceiver item env :: stack, heap⟩
      | _, _ => match base with
        | .name name => if (env name).isSome then
            .next ⟨.expr base env, .methodReceiver field expressions env :: stack, heap⟩
          else .next (argumentsState (.call (name ++ "." ++ field)) env [] expressions stack heap)
        | _ => .next ⟨.expr base env, .methodReceiver field expressions env :: stack, heap⟩ := by
  simp only [step]
  repeat' (first | simp_all | split)

theorem step_call_expression_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (callee : Expr) (expressions : List Expr) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.expr (.call callee expressions) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.expr (.call callee expressions) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.expr (.call callee expressions) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have envInside : EnvWithin logical.length env := inside.1
  have stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame := inside.2
  have argumentsInside (operation : Operation) (arguments : List Expr)
      (bounded : OperationWithin logical.length operation) :
      StateWithin (argumentsState operation env [] arguments stack logical) :=
    argumentsState_within logical operation env [] arguments stack bounded envInside (by simp) stackInside
  cases callee with
  | name name =>
    apply Preserves.unchanged layout
    · exact argumentsState_heap ..
    · exact argumentsInside _ _ (by trivial)
    · simpa only [step, relocateState, relocateWork, relocateStep, relocateRuntimeOperation, List.map_nil] using
        congrArg Step.next (argumentsState_relocates rename logical physical (.call name) env [] expressions stack)
  | «attribute» base field =>
    simp only [relocateState, relocateWork, step_attribute_call, relocateEnv, Option.isSome_map]
    split
    all_goals repeat' (first | split | simp_all only)
    all_goals apply Preserves.unchanged layout
    all_goals first
      | exact argumentsState_heap ..
      | exact argumentsInside _ _ (by trivial)
      | rfl
      | exact congrArg Step.next (argumentsState_relocates rename logical physical (.call _) env [] _ stack)
      | (simp [StepWithin, StateWithin, WorkWithin, FrameWithin, envInside] <;> exact stackInside)
      | simp [relocateStep, relocateState, relocateWork, relocateFrame]
  | _ =>
    apply Preserves.unchanged layout <;>
      simp [step, StepHeap, StepWithin, relocateState, relocateWork, relocateStep]

theorem step_builtin_expression_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (name : Builtin) (expressions : List Expr) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.expr (.builtinCall name expressions) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.expr (.builtinCall name expressions) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.expr (.builtinCall name expressions) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · exact argumentsState_heap ..
  · exact argumentsState_within logical (.builtin name) env [] expressions stack (by trivial) inside.1 (by simp) inside.2
  · simpa only [step, relocateState, relocateWork, relocateStep, relocateRuntimeOperation, List.map_nil] using
      congrArg Step.next (argumentsState_relocates rename logical physical (.builtin name) env [] expressions stack)

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.HeapCalls

/-- A successful name evaluation implies a bound local; a missing name terminates immediately. -/
theorem Evaluates.name_isSome
    {module : Module} {globals : Mutable.Globals} {env : Env} {name : String}
    {heap after : Mutable.Heap} {value : Mutable.Value}
    (evaluated : Evaluates (globals := globals) module env (.name name) heap value after) :
    (env name).isSome = true := by
  cases found : env name with
  | some value => rfl
  | none =>
    have reached := evaluated heap.length []
    cases reached with
    | next transition _ => simp [step, found, done, protectGenerator] at transition

/-- Receiver effects precede binding, and argument effects precede execution of the captured method. -/
theorem Evaluates.method_receiver
    {module : Module} {globals : Mutable.Globals} {env : Env} {base : Expr} {field : String}
    {expressions : List Expr} {heap afterReceiver afterArguments finalHeap : Mutable.Heap}
    {receiver value : Mutable.Value} {values : List Mutable.Value} {args : List Arg} {body : List Stmt}
    (target : Evaluates (globals := globals) module env base heap receiver afterReceiver)
    (ordinary : field ≠ "append" ∧ field ≠ "add")
    (bound : bindMethod module receiver field afterReceiver = some (.ok (.method receiver args body), afterReceiver))
    (arguments : Evaluates.Arguments (globals := globals) module env expressions afterReceiver values afterArguments)
    (execution : MethodReturns (globals := globals) module receiver args body values afterArguments value finalHeap) :
    Evaluates (globals := globals) module env (.call (.attribute base field) expressions) heap value finalHeap := by
  intro anchors stack
  apply Reaches.next (following := ⟨.expr base env, .methodReceiver field expressions env :: stack, heap⟩)
  · rw [Relocation.step_attribute_call]
    cases base with
    | name name => simp [ordinary.1, ordinary.2, target.name_isSome]
    | _ => simp [ordinary.1, ordinary.2]
  apply (target anchors _).trans
  apply Reaches.next (following := argumentsState (.method receiver args body) env [] expressions stack afterReceiver)
    (by simp [step, run, bound])
  exact (Evaluates.arguments_reach arguments (.method receiver args body) [] anchors stack).trans
    (execution anchors stack)

end FormalSW.PyAst.HeapCalls
