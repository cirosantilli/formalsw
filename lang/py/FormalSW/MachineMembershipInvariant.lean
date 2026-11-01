import lang.py.FormalSW.MembershipUnsupported
import lang.py.FormalSW.MachineExpressionInvariant

/-! Membership retains saved consumers, exceptions and unsupported search outcomes. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem result_membership_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (needle container : Value) (negated : Bool)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (needleInside : needle.edge.Within logical.length) (containerInside : container.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (HeapCalls.membership needle container negated) stack globals)
      (result physicalAnchors physical
        (HeapCalls.membership (relocateValue rename needle) (relocateValue rename container) negated)
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  apply result_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _ stack globals layout
    stackInside globalsInside
  · intro outcome after executed
    refine ⟨membership_keeps_heap logical after layout.closed needle container negated needleInside containerInside
      outcome executed, ?_⟩
    intro returned success
    rw [success] at executed
    obtain ⟨answer, rfl⟩ := membership_value logical after needle container negated returned executed
    trivial
  · exact layout.runtime.membership_complete layout.closed needle container negated needleInside containerInside

theorem step_membership_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (needle container : Value) (negated : Bool)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation (.membership negated) [needle, container], stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.membership negated) [needle, container], stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.operation (.membership negated) [needle, container], stack, logical⟩)
        (relocateGlobals rename globals)) := by
  exact (result_membership_preserves logical physical rename logicalAnchors physicalAnchors needle container negated
    stack globals layout (inside.1.2 needle (by simp)) (inside.1.2 container (by simp)) inside.2 globalsInside
    ).protectGenerator stack inside.2

/-- Scalar membership is a specialization of the unrestricted rule. -/
theorem step_membership_scalar_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (needle : Constant) (container : Value) (negated : Bool)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation (.membership negated) [.scalar needle, container], stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.membership negated) [.scalar needle, container], stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.operation (.membership negated) [.scalar needle, container], stack, logical⟩)
        (relocateGlobals rename globals)) :=
  step_membership_preserves module logical physical rename logicalAnchors physicalAnchors (.scalar needle) container
    negated stack globals layout inside globalsInside

theorem step_membership_expression_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (needle container : Expr) (negated : Bool) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.expr (.membership needle container negated) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.expr (.membership needle container negated) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.expr (.membership needle container negated) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · rfl
  · exact argumentsState_within logical (.membership negated) env [] [needle, container] stack
      (by trivial) inside.1 (by simp) inside.2
  · simp only [step, argumentsState, relocateState, relocateWork, List.map_cons, List.map_nil,
      relocateFrame, relocateOperation, relocateRuntimeOperation, protectGenerator_next, relocateStep]

end FormalSW.PyAst.HeapCalls.Relocation
