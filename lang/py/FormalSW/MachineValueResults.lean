import lang.py.FormalSW.MachineItemInvariant

/-! Constructor and comprehension results retain their destinations across operand effects. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

variable (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
  (logicalAnchors physicalAnchors : Nat)

theorem step_comprehensionResult_preserves (value : Value) (address : Nat) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .comprehensionResult address :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .comprehensionResult address :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .comprehensionResult address :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have destination := inside.2 (.comprehensionResult address) (List.mem_cons_self ..)
  simp only [FrameWithin] at destination
  apply Preserves.unchanged layout
  · rfl
  · exact ⟨destination, fun frame member => inside.2 frame (List.mem_cons_of_mem _ member)⟩
  · simp [step, relocateState, relocateWork, relocateFrame, relocateStep, relocateValue]

theorem step_initialized_preserves (value : Value) (address : Nat) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .initialized address :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .initialized address :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .initialized address :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have destination := inside.2 (.initialized address) (List.mem_cons_self ..)
  simp only [FrameWithin] at destination
  have stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame :=
    fun frame member => inside.2 frame (List.mem_cons_of_mem _ member)
  cases value <;> try cases ‹Constant›
  all_goals
    apply Preserves.unchanged layout
    · rfl
    · simp only [step]
      first
      | exact ⟨destination, stackInside⟩
      | (apply protectGenerator_within; exact ⟨globalsInside, by intros; contradiction⟩)
    · simp [step, relocateState, relocateWork, relocateFrame, relocateStep, relocateValue,
        done, relocateCompletion, Except.map, protectGenerator, Calls.generatorException]

theorem step_assignSlice_preserves (value : Value) (base lower upper stride : Expr)
    (rest : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .assignSlice base lower upper stride rest env :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .assignSlice base lower upper stride rest env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .assignSlice base lower upper stride rest env :: stack, logical⟩)
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
  · exact argumentsState_within logical (.setSlice value) env [] [base, lower, upper, stride] (.discard rest env :: stack)
      inside.1 saved.1 (by simp) remainder
  · simp [step, argumentsState, relocateState, relocateWork, relocateFrame, relocateStep,
      relocateOperation, relocateRuntimeOperation]

end FormalSW.PyAst.HeapCalls.Relocation
