import lang.py.FormalSW.MachineBuiltinInvariant

/-! Generator entry retains enclosing scopes, captured locals and suspended boundaries. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem arguments_entry_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat) (anchors : Nat)
    (operation : Operation) (env : Env) (values : List Value) (expressions : List Expr) (stack : List Frame)
    (layout : ExecutionLayout logical physical rename) (operationInside : OperationWithin logical.length operation)
    (envInside : EnvWithin logical.length env) (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) :
    Preserves logical physical rename anchors
      (.next (argumentsState operation env values expressions stack logical))
      (.next (argumentsState (relocateRuntimeOperation rename operation) (relocateEnv rename env)
        (values.map (relocateValue rename)) expressions (stack.map (relocateFrame rename)) physical)) :=
  Preserves.unchanged layout (argumentsState_heap ..)
    (argumentsState_within logical operation env values expressions stack operationInside envInside valuesInside stackInside)
    (congrArg Step.next (argumentsState_relocates rename logical physical operation env values expressions stack))

theorem expandedArgumentsState_relocates (rename : Nat → Nat) (logical physical : Mutable.Heap)
    (operation : Operation) (env : Env) (values : List Value) (expressions : List Expr) (stack : List Frame) :
    expandedArgumentsState (relocateRuntimeOperation rename operation) (relocateEnv rename env)
        (values.map (relocateValue rename)) expressions (stack.map (relocateFrame rename)) physical =
      relocateState rename physical (expandedArgumentsState operation env values expressions stack logical) := by
  cases expressions with
  | nil => rfl
  | cons first rest =>
    cases selected : starSource? first <;>
      simp [expandedArgumentsState, selected, relocateState, relocateWork, relocateFrame]

theorem expanded_arguments_entry_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat) (anchors : Nat)
    (operation : Operation) (env : Env) (values : List Value) (expressions : List Expr) (stack : List Frame)
    (layout : ExecutionLayout logical physical rename) (operationInside : OperationWithin logical.length operation)
    (envInside : EnvWithin logical.length env) (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) :
    Preserves logical physical rename anchors
      (.next (expandedArgumentsState operation env values expressions stack logical))
      (.next (expandedArgumentsState (relocateRuntimeOperation rename operation) (relocateEnv rename env)
        (values.map (relocateValue rename)) expressions (stack.map (relocateFrame rename)) physical)) := by
  apply Preserves.unchanged layout
  · cases expressions with
    | nil => rfl
    | cons first rest => cases selected : starSource? first <;> simp [expandedArgumentsState, selected, StepHeap]
  · cases expressions with
    | nil => exact ⟨⟨operationInside, valuesInside⟩, stackInside⟩
    | cons first rest =>
      cases selected : starSource? first <;> simp only [expandedArgumentsState, selected]
      all_goals
        refine ⟨envInside, ?_⟩
        intro frame member
        rcases List.mem_cons.mp member with rfl | member
        · simp only [FrameWithin]
          exact ⟨envInside, operationInside, valuesInside⟩
        · exact stackInside frame member
  · exact congrArg Step.next (expandedArgumentsState_relocates rename logical physical operation env values expressions stack)

theorem withoutGenerator_within (limit : Nat) (stack : List Frame)
    (inside : ∀ frame ∈ stack, FrameWithin limit frame) :
    ∀ frame ∈ withoutGenerator stack, FrameWithin limit frame := by
  induction stack with
  | nil => simp [withoutGenerator]
  | cons frame rest ih =>
    have saved : ∀ frame ∈ rest, FrameWithin limit frame := fun frame member => inside frame (List.mem_cons_of_mem _ member)
    have head := inside frame (List.mem_cons_self ..)
    cases frame <;> simp only [withoutGenerator]
    all_goals first
      | exact saved
      | (intro frame member; rcases List.mem_cons.mp member with rfl | member; exact head; exact ih saved frame member)

theorem withoutGenerator_relocates (rename : Nat → Nat) (stack : List Frame) :
    withoutGenerator (stack.map (relocateFrame rename)) = (withoutGenerator stack).map (relocateFrame rename) := by
  induction stack with
  | nil => rfl
  | cons frame rest ih => cases frame <;> simp only [List.map_cons, relocateFrame, withoutGenerator, ih]

variable (logical physical : Mutable.Heap) (rename : Nat → Nat) (anchors : Nat)
  (env : Env) (stack : List Frame) (layout : ExecutionLayout logical physical rename)
  (envInside : EnvWithin logical.length env) (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)

include layout envInside stackInside

theorem generator_arguments_preserves (action : GeneratorAction) (element : Expr)
    (generators : List (Expr × Expr × List Expr)) :
    Preserves logical physical rename anchors
      (.next (generatorArguments action element generators env stack logical))
      (.next (generatorArguments action element generators (relocateEnv rename env) (stack.map (relocateFrame rename)) physical)) := by
  unfold generatorArguments
  rw [SetCalls.Relocation.comprehensionTargetsEnv_relocates]
  exact arguments_entry_preserves logical physical rename anchors _ env [] _ stack layout
    (SetCalls.Relocation.comprehensionTargetsEnv_within logical.length env generators envInside)
    envInside (by simp) stackInside

theorem truth_generator_arguments_preserves (universal : Bool) (element : Expr)
    (generators : List (Expr × Expr × List Expr)) :
    Preserves logical physical rename anchors
      (.next (truthGeneratorArguments universal element generators env stack logical))
      (.next (truthGeneratorArguments universal element generators (relocateEnv rename env) (stack.map (relocateFrame rename)) physical)) := by
  unfold truthGeneratorArguments
  rw [SetCalls.Relocation.comprehensionTargetsEnv_relocates]
  exact arguments_entry_preserves logical physical rename anchors _ env [] _ stack layout
    (SetCalls.Relocation.comprehensionTargetsEnv_within logical.length env generators envInside)
    envInside (by simp) stackInside

theorem extremum_generator_arguments_preserves (maximum : Bool) (fallback : Option Expr) (element : Expr)
    (generators : List (Expr × Expr × List Expr)) :
    Preserves logical physical rename anchors
      (.next (extremumGeneratorArguments maximum fallback element generators env stack logical))
      (.next (extremumGeneratorArguments maximum fallback element generators (relocateEnv rename env) (stack.map (relocateFrame rename)) physical)) := by
  unfold extremumGeneratorArguments
  exact arguments_entry_preserves logical physical rename anchors _ env [] _ stack layout
    envInside envInside (by simp) stackInside

theorem next_generator_arguments_preserves (fallback : Option Expr) (element : Expr)
    (generators : List (Expr × Expr × List Expr)) :
    Preserves logical physical rename anchors
      (.next (nextGeneratorArguments fallback element generators env stack logical))
      (.next (nextGeneratorArguments fallback element generators (relocateEnv rename env) (stack.map (relocateFrame rename)) physical)) := by
  unfold nextGeneratorArguments
  exact arguments_entry_preserves logical physical rename anchors _ env [] _ stack layout
    envInside envInside (by simp) stackInside

omit layout envInside stackInside

inductive GeneratorEntry where
  | unsupported
  | expanded (name : String) (expressions : List Expr)
  | resume
  | exhausted
  | next (fallback : Option Expr)
  | extremum (maximum : Bool) (fallback : Option Expr)
  | truth (universal : Bool)
  | collect (action : GeneratorAction)
  | tuple
  | join (receiver : Expr)

def generatorEntry (consumer element : Expr) (generators : List (Expr × Expr × List Expr)) : GeneratorEntry :=
  match consumer, element, generators with
  | .call (.name "$formalsw.star.call") [], .call (.name name) expressions, [] => .expanded name expressions
  | .call (.name "$formalsw.extremum.compare") [], _, [] => .resume
  | .call (.name "$formalsw.next.exhausted") [], .constant .none, [] => .exhausted
  | .call (.name "$formalsw.next.generator") [], _, _ => .next none
  | .call (.name "$formalsw.next.generator") [fallback], _, _ => .next (some fallback)
  | .call (.name "$formalsw.max.generator") [], _, _ => .extremum true none
  | .call (.name "$formalsw.min.generator") [], _, _ => .extremum false none
  | .call (.name "$formalsw.max.generator") [fallback], _, _ => .extremum true (some fallback)
  | .call (.name "$formalsw.min.generator") [fallback], _, _ => .extremum false (some fallback)
  | .builtinCall .all [], _, _ => .truth true
  | .builtinCall .any [], _, _ => .truth false
  | .builtinCall .list [], _, _ => .collect .list
  | .builtinCall .tuple [], _, _ => .tuple
  | .builtinCall .sorted [], _, _ => .collect .sorted
  | .builtinCall .sortedReverse [.constant (.bool reverse)], _, _ => .collect (.sortedReverse reverse)
  | .attribute receiver "join", _, _ => .join receiver
  | _, _, _ => .unsupported

def generatorEntryStep (entry : GeneratorEntry) (element : Expr)
    (generators : List (Expr × Expr × List Expr)) (env : Env) (stack : List Frame) (heap : Mutable.Heap) :
    Step State Mutable.Completion :=
  match entry with
  | .unsupported => .unsupported
  | .expanded name expressions => .next (expandedArgumentsState (.call name) env [] expressions stack heap)
  | .resume => .next ⟨.expr element env, .extremumResume stack :: withoutGenerator stack, heap⟩
  | .exhausted => .next ⟨.operation (.raiseException "StopIteration") [], withoutGenerator stack, heap⟩
  | .next fallback => .next (nextGeneratorArguments fallback element generators env stack heap)
  | .extremum maximum fallback => .next (extremumGeneratorArguments maximum fallback element generators env stack heap)
  | .truth universal => .next (truthGeneratorArguments universal element generators env stack heap)
  | .collect action => .next (generatorArguments action element generators env stack heap)
  | .tuple => .next ⟨.expr (.builtinCall .tuple [.consumeGenerator (.builtinCall .list []) element generators]) env, stack, heap⟩
  | .join receiver => .next ⟨.expr receiver env, .generatorReceiver element generators env :: stack, heap⟩

theorem step_generator_entry (module : Module) (anchors : Nat) (consumer element : Expr)
    (generators : List (Expr × Expr × List Expr)) (env : Env) (stack : List Frame) (heap : Mutable.Heap)
    (globals : Mutable.Globals) :
    step module anchors ⟨.expr (.consumeGenerator consumer element generators) env, stack, heap⟩ globals =
      generatorEntryStep (generatorEntry consumer element generators) element generators env stack heap := by
  simp only [step, generatorEntry, generatorEntryStep]
  repeat' (first | simp_all | split)


end FormalSW.PyAst.HeapCalls.Relocation
