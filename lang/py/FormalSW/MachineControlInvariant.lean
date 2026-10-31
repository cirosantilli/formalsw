import lang.py.FormalSW.MachineStatementInvariant

/-! Truth-dependent expression entry retains the same saved roots as its continuation. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

variable (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
  (logicalAnchors physicalAnchors : Nat)

theorem step_boolean_expression_preserves (op : BoolOp) (expressions : List Expr)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.expr (.boolOp op expressions) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.expr (.boolOp op expressions) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.expr (.boolOp op expressions) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases expressions with
  | nil =>
    apply Preserves.unchanged layout <;> trivial
  | cons first rest =>
    apply Preserves.unchanged layout
    · rfl
    · refine ⟨inside.1, ?_⟩
      intro frame member
      rcases List.mem_cons.mp member with rfl | member
      · simpa only [FrameWithin] using inside.1
      · exact inside.2 frame member
    · simp only [step, relocateState, relocateWork, relocateStep, relocateFrame, protectGenerator_next, List.map_cons]

theorem step_conditional_expression_preserves (condition yes no : Expr)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.expr (.ifExp condition yes no) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.expr (.ifExp condition yes no) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.expr (.ifExp condition yes no) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · rfl
  · refine ⟨inside.1, ?_⟩
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [FrameWithin] using inside.1
    · exact inside.2 frame member
  · simp only [step, relocateState, relocateWork, relocateStep, relocateFrame, protectGenerator_next, List.map_cons]

end FormalSW.PyAst.HeapCalls.Relocation
