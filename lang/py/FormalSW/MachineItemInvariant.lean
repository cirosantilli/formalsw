import lang.py.FormalSW.ItemWriteRelocation
import lang.py.FormalSW.MachineExpressionInvariant

/-! Indexed access preserves shared objects, saved operands, and iterator consumers. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem step_subscript_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (receiver index : Value) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation .subscript [receiver, index], stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation .subscript [receiver, index], stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.operation .subscript [receiver, index], stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have receiverInside := inside.1.2 receiver (by simp)
  have indexInside := inside.1.2 index (by simp)
  exact (result_readonly_preserves logical physical rename logicalAnchors physicalAnchors
    (Mutable.getItem receiver index) (Mutable.getItem (relocateValue rename receiver) (relocateValue rename index))
    stack globals layout inside.2 globalsInside
    (fun outcome after => getItem_effect logical after layout.closed receiver index receiverInside indexInside outcome)
    (RuntimeLayout.getItem logical physical rename layout.runtime layout.closed receiver index receiverInside indexInside)
    ).protectGenerator stack inside.2

theorem step_subscript_expression_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (base index : Expr) (env : Env) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.expr (.subscript base index) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.expr (.subscript base index) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.expr (.subscript base index) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · cases index <;> exact argumentsState_heap ..
  · cases index <;> exact argumentsState_within logical _ env [] _ stack
      (by simp [OperationWithin]) inside.1 (by simp) inside.2
  · cases index <;> simp [step, argumentsState, relocateState, relocateWork, relocateFrame,
      relocateStep, relocateOperation, relocateRuntimeOperation]

theorem step_augmentItemIndex_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (receiver index : Value) (op : BinOp) (right : Expr)
    (rest : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value index, .augmentItemIndex receiver op right rest env :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value index, .augmentItemIndex receiver op right rest env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value index, .augmentItemIndex receiver op right rest env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have saved := inside.2 _ (List.mem_cons_self ..)
  simp only [FrameWithin] at saved
  have paired := RuntimeLayout.getItem logical physical rename layout.runtime layout.closed receiver index saved.1 inside.1
  cases executed : Mutable.getItem receiver index logical with
  | none =>
    apply Preserves.unchanged layout <;>
      simp [step, run, executed, paired, protectGenerator, StepHeap, StepWithin, relocateState,
        relocateWork, relocateFrame, relocateStep]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    obtain ⟨same, bounded⟩ := getItem_effect logical after layout.closed receiver index saved.1 inside.1 outcome executed
    subst after
    apply Preserves.unchanged layout
    · apply protectGenerator_heap
      cases outcome <;> simp [run, executed, done, StepHeap]
    · apply protectGenerator_within
      cases outcome with
      | error exception =>
        simp only [run, executed, done, StepWithin]
        exact ⟨globalsInside, by intro value impossible; cases impossible⟩
      | ok previous =>
        simp only [run, executed, StepWithin]
        refine ⟨saved.2.1, ?_⟩
        intro frame member
        rcases List.mem_cons.mp member with rfl | member
        · simpa only [FrameWithin] using bounded previous rfl
        · rcases List.mem_cons.mp member with rfl | member
          · simp only [FrameWithin]
            exact ⟨saved.1, inside.1, saved.2⟩
          · exact inside.2 frame (List.mem_cons_of_mem _ member)
    · cases outcome <;>
        simp [step, run, paired, executed, done, relocateState, relocateWork, relocateFrame,
          relocateStep, relocateCompletion, protectGenerator, Calls.generatorException, Except.map,
          relocateFrame_inGenerator] <;> rfl

theorem step_augmentItemReceiver_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (receiver : Value) (index right : Expr) (op : BinOp)
    (rest : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value receiver, .augmentItemReceiver index op right rest env :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value receiver, .augmentItemReceiver index op right rest env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value receiver, .augmentItemReceiver index op right rest env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have saved := inside.2 _ (List.mem_cons_self ..)
  simp only [FrameWithin] at saved
  apply Preserves.unchanged layout
  · rfl
  · refine ⟨saved.1, ?_⟩
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simp only [FrameWithin]
      exact ⟨inside.1, saved⟩
    · exact inside.2 frame (List.mem_cons_of_mem _ member)
  · simp [step, relocateState, relocateWork, relocateFrame, relocateStep]

theorem step_assignItem_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (base index : Expr)
    (rest : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .assignItem base index rest env :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .assignItem base index rest env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .assignItem base index rest env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have saved := inside.2 _ (List.mem_cons_self ..)
  simp only [FrameWithin] at saved
  have remainder : ∀ frame ∈ .discard rest env :: stack, FrameWithin logical.length frame := by
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [FrameWithin] using saved
    · exact inside.2 frame (List.mem_cons_of_mem _ member)
  apply Preserves.unchanged layout
  · rfl
  · exact argumentsState_within logical (.setItem value) env [] [base, index] (.discard rest env :: stack)
      inside.1 saved.1 (by simp) remainder
  · simp [step, argumentsState, relocateState, relocateWork, relocateFrame, relocateStep,
      relocateOperation, relocateRuntimeOperation]

theorem result_setItem_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (receiver index value : Value) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (receiverInside : receiver.edge.Within logical.length) (indexInside : index.edge.Within logical.length)
    (valueInside : value.edge.Within logical.length) (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (Mutable.setItem receiver index value) stack globals)
      (result physicalAnchors physical
        (Mutable.setItem (relocateValue rename receiver) (relocateValue rename index) (relocateValue rename value))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  cases executed : Mutable.setItem receiver index value logical with
  | none =>
    have other := (layout.runtime.setItem_unsupported layout.closed receiver index value receiverInside indexInside).mpr executed
    apply Preserves.unchanged layout <;> simp [result, run, executed, other, StepHeap, StepWithin, relocateStep]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    obtain ⟨other, paired, retained⟩ := layout.setItem receiver index value receiverInside indexInside valueInside outcome after executed
    have effect := setItem_effect logical after receiver index value outcome executed
    have physicalEffect := setItem_effect physical other (relocateValue rename receiver) (relocateValue rename index)
      (relocateValue rename value) _ paired
    apply result_preserves logical physical after other rename rename logicalAnchors physicalAnchors _ _ stack globals outcome
      (fun _ _ => rfl) (Nat.le_of_eq effect.1.symm) (Nat.le_of_eq physicalEffect.1.symm)
      retained stackInside globalsInside ?_ executed paired
    intro returned success
    rw [effect.2 returned success]
    trivial

theorem step_setItem_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (receiver index value : Value) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation (.setItem value) [receiver, index], stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.setItem value) [receiver, index], stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.operation (.setItem value) [receiver, index], stack, logical⟩)
        (relocateGlobals rename globals)) := by
  exact (result_setItem_preserves logical physical rename logicalAnchors physicalAnchors receiver index value stack globals layout
    (inside.1.2 receiver (by simp)) (inside.1.2 index (by simp)) inside.1.1 inside.2 globalsInside).protectGenerator stack inside.2

theorem step_writeItem_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (receiver index value : Value) (rest : List Stmt) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .writeItem receiver index rest env :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .writeItem receiver index rest env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .writeItem receiver index rest env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have saved := inside.2 _ (List.mem_cons_self ..)
  simp only [FrameWithin] at saved
  have remainder : ∀ frame ∈ .discard rest env :: stack, FrameWithin logical.length frame := by
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [FrameWithin] using saved.2.2
    · exact inside.2 frame (List.mem_cons_of_mem _ member)
  simpa only [step, relocateState, relocateWork, List.map_cons, relocateFrame] using
    (result_setItem_preserves logical physical rename logicalAnchors physicalAnchors receiver index value
      (.discard rest env :: stack) globals layout saved.1 saved.2.1 inside.1 remainder globalsInside).protectGenerator _ inside.2

end FormalSW.PyAst.HeapCalls.Relocation
