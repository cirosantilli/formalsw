import lang.py.FormalSW.IteratorInvariant

/-! Ordinary interpreter steps feed the invariant used by set and iterator execution. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

def StepHeap (heap : Mutable.Heap) : Step State Mutable.Completion → Prop
  | .next state => state.heap = heap
  | .done (.ok completion) => completion.heap = heap
  | .done (.error _) | .unsupported => True

def Preserves (logical physical : Mutable.Heap) (rename : Nat → Nat) (anchors : Nat)
    (left right : Step State Mutable.Completion) : Prop :=
  ∃ logicalAfter physicalAfter nextMap,
    (∀ address < logical.length, nextMap address = rename address) ∧
    logical.length ≤ logicalAfter.length ∧ physical.length ≤ physicalAfter.length ∧
    ExecutionLayout logicalAfter physicalAfter nextMap ∧ StepHeap logicalAfter left ∧ StepWithin left ∧
    right = relocateStep nextMap physicalAfter anchors left

theorem Preserves.unchanged {logical physical : Mutable.Heap} {rename : Nat → Nat} {anchors : Nat}
    {left right : Step State Mutable.Completion} (layout : ExecutionLayout logical physical rename)
    (heap : StepHeap logical left) (inside : StepWithin left)
    (paired : right = relocateStep rename physical anchors left) : Preserves logical physical rename anchors left right :=
  ⟨logical, physical, rename, fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _, layout, heap, inside, paired⟩

theorem protectGenerator_heap (heap : Mutable.Heap) (stack : List Frame) (transition : Step State Mutable.Completion)
    (retained : StepHeap heap transition) : StepHeap heap (protectGenerator stack transition) := by
  cases transition with
  | next | unsupported => exact retained
  | done outcome =>
    cases outcome with
    | error => trivial
    | ok completion =>
      rcases completion with ⟨outcome, globals, after, anchors⟩
      cases outcome <;> exact retained

theorem argumentsState_heap (heap : Mutable.Heap) (operation : Operation) (env : Env)
    (values : List Value) (expressions : List Expr) (stack : List Frame) :
    (argumentsState operation env values expressions stack heap).heap = heap := by
  cases expressions <;> rfl

theorem step_method_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (receiver : Value) (args : List Arg) (body : List Stmt)
    (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation (.method receiver args body) values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.method receiver args body) values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation (.method receiver args body) values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · apply protectGenerator_heap
    cases completed : completeArguments args (receiver :: values) <;>
      simp [invokeMethod, completed, done, StepHeap]
  · cases completed : completeArguments args (receiver :: values) with
    | none =>
      simp only [step, invokeMethod, completed]
      apply protectGenerator_within
      exact ⟨globalsInside, by intro value impossible; cases impossible⟩
    | some filled =>
      have entered : step module logicalAnchors ⟨.operation (.method receiver args body) values, stack, logical⟩ globals =
          .next ⟨.block (executableBody body) (functionEnv args body filled globals), stack, logical⟩ := by
        simp [step, invokeMethod, completed]
      rw [entered]
      exact step_method_within module logical logicalAnchors receiver args body values stack globals _ inside globalsInside entered
  · exact step_method_relocate module rename logical physical logicalAnchors physicalAnchors receiver args body values stack globals

theorem step_call_preserves (module : Module) (name : String) (args : List Arg) (body : List Stmt)
    (found : findFunctionIn module.body name = some (args, body))
    (source : ∀ statement ∈ body, StmtWithin 0 statement)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation (.call name) values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.call name) values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation (.call name) values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · apply protectGenerator_heap
    cases completed : completeArguments args values <;> simp [found, completed, done, StepHeap]
  · cases completed : completeArguments args values with
    | none =>
      simp only [step, found, completed]
      apply protectGenerator_within
      exact ⟨globalsInside, by intro value impossible; cases impossible⟩
    | some filled =>
      have entered : step module logicalAnchors ⟨.operation (.call name) values, stack, logical⟩ globals =
          .next ⟨.block (executableBody body) (functionEnv args body filled globals), stack, logical⟩ := by
        simp [step, found, completed]
      rw [entered]
      exact step_call_within module name args body found source logical logicalAnchors values stack globals _ inside globalsInside entered
  · exact step_call_relocate module name args body found source rename logical physical logicalAnchors physicalAnchors values stack globals

theorem step_list_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (items : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation .list items, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation .list items, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation .list items, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have allocated := step_list_relocates module logical physical rename layout logicalAnchors physicalAnchors
    items stack globals inside.1.2 inside.2 globalsInside
  refine ⟨logical ++ [.list items], physical ++ [.list (items.map (relocateValue rename))],
    extendMap rename logical.length physical.length, extendMap_old rename logical.length physical.length,
    by simp, by simp, allocated.2.2.1, ?_, ?_, ?_⟩
  · rw [allocated.1]; rfl
  · rw [allocated.1]; exact allocated.2.2.2.1
  · rw [allocated.1]; exact allocated.2.1

theorem step_assign_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (name : String) (body : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .assign name body env :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .assign name body env :: stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.value value, .assign name body env :: stack, logical⟩)
        (relocateGlobals rename globals)) :=
  Preserves.unchanged layout rfl (StateWithin.assign logical value name body env stack inside)
    (step_assign_relocates module logical physical rename logicalAnchors physicalAnchors value name body env stack globals)

theorem step_arguments_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (operation : Operation) (values : List Value)
    (rest : List Expr) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .arguments operation values rest env :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .arguments operation values rest env :: stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.value value, .arguments operation values rest env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · cases rest <;> rfl
  · cases rest <;> exact StateWithin.arguments logical value operation values _ env stack inside
  · exact step_arguments_relocates module logical physical rename logicalAnchors physicalAnchors value operation values rest env stack globals

theorem step_boolean_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (op : BoolOp) (rest : List Expr) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .boolean op rest env :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .boolean op rest env :: stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.value value, .boolean op rest env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · obtain ⟨truth, tested⟩ := truth_total logical value inside.1
    cases op <;> cases truth <;> cases rest <;> simp [step, run, tested, StepHeap]
  · exact StateWithin.boolean module logical logicalAnchors value op rest env stack globals inside
  · exact step_boolean_relocates module logical physical rename layout.runtime logicalAnchors physicalAnchors value op rest env stack globals inside.1

theorem step_conditional_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (yes no : Expr) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .conditional yes no env :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .conditional yes no env :: stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.value value, .conditional yes no env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · obtain ⟨truth, tested⟩ := truth_total logical value inside.1
    simp [step, run, tested, StepHeap]
  · exact StateWithin.conditional module logical logicalAnchors value yes no env stack globals inside
  · exact step_conditional_relocates module logical physical rename layout.runtime logicalAnchors physicalAnchors value yes no env stack globals inside.1

theorem step_branch_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (yes no following : List Stmt) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .branch yes no following env :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .branch yes no following env :: stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.value value, .branch yes no following env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · obtain ⟨truth, tested⟩ := truth_total logical value inside.1
    cases truth <;> simp [step, run, tested, StepHeap]
  · exact StateWithin.branch module logical logicalAnchors value yes no following env stack globals inside
  · exact step_branch_relocates module logical physical rename layout.runtime logicalAnchors physicalAnchors value yes no following env stack globals inside.1


theorem step_return_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (expression : Expr) (following : List Stmt) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.block (.return expression :: following) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.return expression :: following) env, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.block (.return expression :: following) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · rfl
  · exact ⟨inside.1.1, inside.2⟩
  · simp [relocateState, relocateWork, relocateStmt, step, relocateStep]

theorem step_lookup_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (name : String) (env : Env) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.expr (.name name) env, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.expr (.name name) env, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.expr (.name name) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · cases found : env name <;> simp [step, found, done, protectGenerator, StepHeap]
  · cases found : env name with
    | none =>
      simp only [step, found]
      apply protectGenerator_within
      exact ⟨globalsInside, by intro value impossible; cases impossible⟩
    | some value =>
      simp only [step, found, protectGenerator_next, StepWithin]
      exact ⟨inside.1 name value found, inside.2⟩
  · exact step_lookup_relocates module logical physical rename logicalAnchors physicalAnchors name env stack globals

theorem step_constant_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Constant) (env : Env) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.expr (.constant value) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.expr (.constant value) env, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.expr (.constant value) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · rfl
  · exact ⟨by trivial, inside.2⟩
  · exact step_constant_relocates module logical physical rename logicalAnchors physicalAnchors value env stack globals

theorem step_list_expression_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (expressions : List Expr) (env : Env) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.expr (.list expressions) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.expr (.list expressions) env, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.expr (.list expressions) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · cases expressions <;> rfl
  · cases expressions <;> exact argumentsState_within logical .list env [] _ stack (by trivial) inside.1 (by simp) inside.2
  · cases expressions <;> simp [relocateState, relocateWork, step, argumentsState, relocateStep, relocateFrame, relocateRuntimeOperation, relocateOperation]

theorem step_value_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (inside : value.edge.Within logical.length)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, [], logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.value value, [], logical⟩) (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · rfl
  · exact ⟨globalsInside, by intro result same; cases same; exact inside⟩
  · rfl

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.SetCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation
open IteratorCalls.Relocation (relocateCore)

/-- Supported core steps retain their invariant through the set-choice wrapper. -/
theorem lift_preserves {logical physical : Mutable.Heap} {rename : Nat → Nat} {anchors : Nat}
    {left right : Step HeapCalls.State Mutable.Completion}
    (preserved : HeapCalls.Relocation.Preserves logical physical rename anchors left right) (used : Nat) :
    Preserves logical physical rename anchors (liftStep used left) (liftStep used right) := by
  obtain ⟨logicalAfter, physicalAfter, nextMap, agree, grows, physicalGrows, layout, heap, inside, paired⟩ := preserved
  refine ⟨logicalAfter, physicalAfter, nextMap, agree, grows, physicalGrows, layout, ?_, ?_, ?_⟩
  · cases left with
    | next | unsupported => exact heap
    | done outcome => cases outcome <;> exact heap
  · cases left with
    | next | unsupported => exact inside
    | done outcome => cases outcome <;> exact inside
  · rw [paired]
    exact IteratorCalls.Relocation.set_lift_relocates nextMap physicalAfter anchors used left

/-- An unsupported ordinary step still takes the actual modeled set fallback. -/
theorem step_preserves_of_heap (module : Module) (choices : ChoiceSchedule) (core : SetCalls.State)
    (physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (globals : Mutable.Globals) (layout : ExecutionLayout core.core.heap physical rename)
    (inside : HeapCalls.Relocation.StateWithin core.core) (globalsInside : GlobalsWithin core.core.heap.length globals)
    (preserved : HeapCalls.Relocation.Preserves core.core.heap physical rename physicalAnchors
      (HeapCalls.step module logicalAnchors core.core globals)
      (HeapCalls.step module physicalAnchors (HeapCalls.Relocation.relocateState rename physical core.core) (relocateGlobals rename globals))) :
    Preserves core.core.heap physical rename physicalAnchors (SetCalls.step module logicalAnchors choices core globals)
      (SetCalls.step module physicalAnchors choices (relocateCore rename physical core) (relocateGlobals rename globals)) := by
  by_cases unsupported : HeapCalls.step module logicalAnchors core.core globals = .unsupported
  · obtain ⟨_, _, _, _, _, _, _, _, _, paired⟩ := preserved
    have other : HeapCalls.step module physicalAnchors (HeapCalls.Relocation.relocateState rename physical core.core)
        (relocateGlobals rename globals) = .unsupported := by
      simpa only [unsupported, HeapCalls.Relocation.relocateStep] using paired
    exact step_fallback_preserves module choices core physical rename logicalAnchors physicalAnchors globals layout inside globalsInside unsupported other
  · have paired := preserved
    obtain ⟨_, _, _, _, _, _, _, _, _, same⟩ := paired
    have other : HeapCalls.step module physicalAnchors (HeapCalls.Relocation.relocateState rename physical core.core)
        (relocateGlobals rename globals) ≠ .unsupported := by
      rw [same]
      cases transition : HeapCalls.step module logicalAnchors core.core globals <;>
        simp_all [HeapCalls.Relocation.relocateStep]
    rw [IteratorCalls.Relocation.set_step_supported module core.core logicalAnchors core.choicesUsed choices globals _ rfl unsupported]
    change Preserves _ _ _ _ _ (SetCalls.step module physicalAnchors choices
      ⟨HeapCalls.Relocation.relocateState rename physical core.core, core.choicesUsed⟩ (relocateGlobals rename globals))
    rw [IteratorCalls.Relocation.set_step_supported module _ physicalAnchors core.choicesUsed choices _ _ rfl other]
    exact lift_preserves preserved core.choicesUsed

end FormalSW.PyAst.SetCalls.Relocation
