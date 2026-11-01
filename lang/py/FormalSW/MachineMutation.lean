import lang.py.FormalSW.MachineAllocation
import lang.py.FormalSW.SequenceRelocation

/-! Mutation steps preserve shared objects and suspended execution. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

/-- Reference bounds also matter when an exception terminates execution. -/
def CompletionWithin (completion : Mutable.Completion) : Prop :=
  GlobalsWithin completion.heap.length completion.globals ∧
  ∀ value, completion.outcome = .ok value → value.edge.Within completion.heap.length

/-- This is a reference invariant, not evidence that a step completes or is supported. -/
def StepWithin : Step State Mutable.Completion → Prop
  | .next state => StateWithin state
  | .done (.ok completion) => CompletionWithin completion
  | .done (.error _) | .unsupported => True

theorem protectGenerator_within (stack : List Frame) (transition : Step State Mutable.Completion)
    (inside : StepWithin transition) : StepWithin (protectGenerator stack transition) := by
  cases transition with
  | next | unsupported => exact inside
  | done outcome =>
    cases outcome with
    | error => trivial
    | ok completion =>
      rcases completion with ⟨outcome, globals, heap, anchors⟩
      cases outcome <;> simpa [protectGenerator, StepWithin, CompletionWithin] using inside

theorem result_within (anchors : Nat) (heap after : Mutable.Heap) (action : Mutable.Eval Value)
    (stack : List Frame) (globals : Mutable.Globals) (outcome : Except ExceptionObject Value)
    (executed : action heap = some (outcome, after)) (larger : heap.length ≤ after.length)
    (valueInside : ∀ value, outcome = .ok value → value.edge.Within after.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin heap.length frame)
    (globalsInside : GlobalsWithin heap.length globals) :
    StepWithin (result (globals := globals) anchors heap action stack) := by
  cases outcome with
  | error exception =>
    simp only [result, run, executed, done, StepWithin, CompletionWithin]
    exact ⟨globalsInside.mono larger, by intro value impossible; cases impossible⟩
  | ok value =>
    simp only [result, run, executed, StepWithin]
    exact value_state_within heap.length after value stack larger (valueInside value rfl) stackInside

theorem step_setField_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
    (receiver value : Value) (name : String) (stack : List Frame) (globals : Mutable.Globals)
    (receiverInside : receiver.edge.Within logical.length) (valueInside : value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals)
    (outcome : Except ExceptionObject Value) (after : Mutable.Heap)
    (executed : Mutable.writeField receiver name value logical = some (outcome, after)) :
    ∃ other, ExecutionLayout after other rename ∧ after.length = logical.length ∧
      step module physicalAnchors
          (relocateState rename physical ⟨.operation (.setField name value) [receiver], stack, logical⟩)
          (relocateGlobals rename globals) =
        relocateStep rename other physicalAnchors
          (step module logicalAnchors ⟨.operation (.setField name value) [receiver], stack, logical⟩ globals) ∧
      StepWithin (step module logicalAnchors ⟨.operation (.setField name value) [receiver], stack, logical⟩ globals) ∧
      GlobalsWithin after.length globals := by
  obtain ⟨other, paired, retained, length, returned⟩ :=
    layout.writeField receiver name value receiverInside valueInside outcome after executed
  refine ⟨other, retained, length, ?_, ?_, length ▸ globalsInside⟩
  · have transported := result_relocates rename logical physical after other logicalAnchors physicalAnchors
      (Mutable.writeField receiver name value)
      (Mutable.writeField (relocateValue rename receiver) name (relocateValue rename value))
      stack globals outcome executed paired
    simp only [relocateState, relocateWork, relocateRuntimeOperation, relocateOperation, List.map_cons,
      List.map_nil, step, primitive]
    rw [transported]
    exact protectGenerator_relocates rename other physicalAnchors stack _
  · apply protectGenerator_within
    exact result_within logicalAnchors logical after _ stack globals outcome executed
      (Nat.le_of_eq length.symm) returned stackInside globalsInside

theorem step_writeAttribute_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
    (receiver value : Value) (name : String) (rest : List Stmt) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals)
    (receiverInside : receiver.edge.Within logical.length) (valueInside : value.edge.Within logical.length)
    (envInside : EnvWithin logical.length env) (restInside : ∀ statement ∈ rest, StmtWithin logical.length statement)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals)
    (outcome : Except ExceptionObject Value) (after : Mutable.Heap)
    (executed : Mutable.writeField receiver name value logical = some (outcome, after)) :
    ∃ other, ExecutionLayout after other rename ∧ after.length = logical.length ∧
      step module physicalAnchors
          (relocateState rename physical ⟨.value value, .writeAttribute receiver name rest env :: stack, logical⟩)
          (relocateGlobals rename globals) =
        relocateStep rename other physicalAnchors
          (step module logicalAnchors ⟨.value value, .writeAttribute receiver name rest env :: stack, logical⟩ globals) ∧
      StepWithin (step module logicalAnchors
        ⟨.value value, .writeAttribute receiver name rest env :: stack, logical⟩ globals) ∧
      GlobalsWithin after.length globals := by
  obtain ⟨other, paired, retained, length, returned⟩ :=
    layout.writeField receiver name value receiverInside valueInside outcome after executed
  refine ⟨other, retained, length, ?_, ?_, length ▸ globalsInside⟩
  · have transported := result_relocates rename logical physical after other logicalAnchors physicalAnchors
      (Mutable.writeField receiver name value)
      (Mutable.writeField (relocateValue rename receiver) name (relocateValue rename value))
      (.discard rest env :: stack) globals outcome executed paired
    simp only [relocateState, relocateWork, List.map_cons, relocateFrame, step]
    simp only [List.map_cons, relocateFrame] at transported
    rw [transported]
    simpa only [List.map_cons, relocateFrame] using
      protectGenerator_relocates rename other physicalAnchors (.writeAttribute receiver name rest env :: stack) _
  · apply protectGenerator_within
    apply result_within logicalAnchors logical after _ (.discard rest env :: stack) globals outcome executed
      (Nat.le_of_eq length.symm) returned _ globalsInside
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [FrameWithin] using And.intro envInside restInside
    · exact stackInside frame member

theorem step_assignAttribute_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (base : Expr) (name : String)
    (rest : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.value value, .assignAttribute base name rest env :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value value, .assignAttribute base name rest env :: stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateFrame, step, argumentsState,
    protectGenerator_next, relocateStep, relocateRuntimeOperation, relocateOperation, List.map_nil]

theorem step_discard_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (rest : List Stmt) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.value value, .discard rest env :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value value, .discard rest env :: stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateFrame, step, protectGenerator_next, relocateStep]

theorem StateWithin.assignAttribute (heap : Mutable.Heap) (value : Value) (base : Expr) (name : String)
    (rest : List Stmt) (env : Env) (stack : List Frame)
    (inside : StateWithin ⟨.value value, .assignAttribute base name rest env :: stack, heap⟩) :
    StateWithin (argumentsState (.setField name value) env [] [base] (.discard rest env :: stack) heap) := by
  have saved := inside.2 (.assignAttribute base name rest env) (by simp)
  simp only [FrameWithin] at saved
  apply argumentsState_within heap (.setField name value) env [] [base] _ inside.1 saved.1 (by simp)
  intro frame member
  rcases List.mem_cons.mp member with rfl | member
  · simpa only [FrameWithin] using saved
  · exact inside.2 frame (by simp [member])

theorem StateWithin.discard (heap : Mutable.Heap) (value : Value) (rest : List Stmt) (env : Env)
    (stack : List Frame) (inside : StateWithin ⟨.value value, .discard rest env :: stack, heap⟩) :
    StateWithin ⟨.block rest env, stack, heap⟩ := by
  have saved := inside.2 (.discard rest env) (by simp)
  simp only [FrameWithin] at saved
  exact ⟨saved, fun frame member => inside.2 frame (by simp [member])⟩

theorem step_setItem_list_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
    (address : Nat) (items : List Value) (subscript replacement : Value)
    (stack : List Frame) (globals : Mutable.Globals)
    (found : logical[address]? = some (.list items))
    (replacementInside : replacement.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals)
    (outcome : Except ExceptionObject Value) (after : Mutable.Heap)
    (executed : Mutable.setItem (.ref address) subscript replacement logical = some (outcome, after)) :
    ∃ other, ExecutionLayout after other rename ∧ after.length = logical.length ∧
      step module physicalAnchors
          (relocateState rename physical ⟨.operation (.setItem replacement) [.ref address, subscript], stack, logical⟩)
          (relocateGlobals rename globals) =
        relocateStep rename other physicalAnchors
          (step module logicalAnchors ⟨.operation (.setItem replacement) [.ref address, subscript], stack, logical⟩ globals) ∧
      StepWithin (step module logicalAnchors
        ⟨.operation (.setItem replacement) [.ref address, subscript], stack, logical⟩ globals) ∧
      GlobalsWithin after.length globals := by
  obtain ⟨other, paired, retained, length, returned⟩ :=
    layout.setItem_list address items subscript replacement found replacementInside outcome after executed
  refine ⟨other, retained, length, ?_, ?_, length ▸ globalsInside⟩
  · have transported := result_relocates rename logical physical after other logicalAnchors physicalAnchors
      (Mutable.setItem (.ref address) subscript replacement)
      (Mutable.setItem (.ref (rename address)) (relocateValue rename subscript) (relocateValue rename replacement))
      stack globals outcome executed paired
    simp only [relocateState, relocateWork, relocateRuntimeOperation, relocateOperation, List.map_cons,
      List.map_nil, relocateValue, step, primitive]
    change protectGenerator (stack.map (relocateFrame rename))
        (result (globals := relocateGlobals rename globals) physicalAnchors physical
          (Mutable.setItem (.ref (rename address)) (relocateValue rename subscript) (relocateValue rename replacement))
          (stack.map (relocateFrame rename))) =
      relocateStep rename other physicalAnchors (protectGenerator stack
        (result (globals := globals) logicalAnchors logical (Mutable.setItem (.ref address) subscript replacement) stack))
    rw [transported]
    exact protectGenerator_relocates rename other physicalAnchors stack _
  · apply protectGenerator_within
    exact result_within logicalAnchors logical after _ stack globals outcome executed
      (Nat.le_of_eq length.symm) returned stackInside globalsInside

theorem step_append_list_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
    (address : Nat) (items : List Value) (value : Value) (stack : List Frame) (globals : Mutable.Globals)
    (found : logical[address]? = some (.list items)) (valueInside : value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    let after := logical.set address (.list (items ++ [value]))
    let other := physical.set (rename address) (.list ((items ++ [value]).map (relocateValue rename)))
    ExecutionLayout after other rename ∧
      step module logicalAnchors ⟨.operation (.append address) [value], stack, logical⟩ globals =
        .next ⟨.value (.scalar .none), stack, after⟩ ∧
      step module physicalAnchors
          (relocateState rename physical ⟨.operation (.append address) [value], stack, logical⟩)
          (relocateGlobals rename globals) =
        .next (relocateState rename other ⟨.value (.scalar .none), stack, after⟩) ∧
      StateWithin ⟨.value (.scalar .none), stack, after⟩ ∧ GlobalsWithin after.length globals := by
  obtain ⟨first, second, retained⟩ := layout.appendItem_list address items value found valueInside
  refine ⟨retained, ?_, ?_, value_state_within logical.length _ _ stack (by simp) (by trivial) stackInside,
    globalsInside.mono (by simp)⟩
  · simp [step, primitive, result, run, first]
  · change protectGenerator (stack.map (relocateFrame rename))
        (result (globals := relocateGlobals rename globals) physicalAnchors physical
          (Mutable.appendItem (rename address) (relocateValue rename value)) (stack.map (relocateFrame rename))) = _
    simp only [result, run, second, protectGenerator_next]
    rfl

end FormalSW.PyAst.HeapCalls.Relocation
