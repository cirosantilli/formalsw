import lang.py.FormalSW.ComparisonUnsupported
import lang.py.FormalSW.MachineExpressionInvariant

/-! Comparison entry and nonrecursive dispatch retain the interpreter invariant. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem result_compare_nonrecursive_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (op : CmpOp) (left right : Value)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (leftInside : left.edge.Within logical.length) (rightInside : right.edge.Within logical.length)
    (nonrecursive : NonrecursiveComparison logical op left right)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (HeapCalls.compare op left right) stack globals)
      (result physicalAnchors physical (HeapCalls.compare op (relocateValue rename left) (relocateValue rename right))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  apply result_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _ stack globals layout
    stackInside globalsInside
  · intro outcome after executed
    obtain ⟨answer, same, unchanged⟩ := compare_effect logical after op left right leftInside rightInside outcome executed
    refine ⟨unchanged, ?_⟩
    intro returned success
    rw [same] at success
    cases answer with
    | error exception => cases success
    | ok answer => cases success; trivial
  · exact layout.runtime.compare_nonrecursive layout.closed op left right leftInside rightInside nonrecursive

theorem step_compare_nonrecursive_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (op : CmpOp) (left right : Value)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value right, .compareRight op left :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals)
    (nonrecursive : NonrecursiveComparison logical op left right) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value right, .compareRight op left :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value right, .compareRight op left :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have leftInside := inside.2 _ (List.mem_cons_self ..)
  simp only [FrameWithin] at leftInside
  have stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame :=
    fun frame member => inside.2 frame (List.mem_cons_of_mem _ member)
  simpa only [step, relocateState, relocateWork, List.map_cons, relocateFrame] using
    (result_compare_nonrecursive_preserves logical physical rename logicalAnchors physicalAnchors op left right stack globals
      layout leftInside inside.1 nonrecursive stackInside globalsInside).protectGenerator _ inside.2

theorem step_chainCompare_nonrecursive_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (op : CmpOp) (left right : Value) (rest : List (CmpOp × Expr)) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value right, .chainRight op left rest env :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals)
    (nonrecursive : NonrecursiveComparison logical op left right) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value right, .chainRight op left rest env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value right, .chainRight op left rest env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have saved := inside.2 _ (List.mem_cons_self ..)
  simp only [FrameWithin] at saved
  have remainder : ∀ frame ∈ .chainResult right rest env :: stack, FrameWithin logical.length frame := by
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [FrameWithin] using And.intro inside.1 saved.2
    · exact inside.2 frame (List.mem_cons_of_mem _ member)
  simpa only [step, relocateState, relocateWork, List.map_cons, relocateFrame] using
    (result_compare_nonrecursive_preserves logical physical rename logicalAnchors physicalAnchors op left right
      (.chainResult right rest env :: stack) globals layout saved.1 inside.1 nonrecursive remainder globalsInside
      ).protectGenerator _ inside.2

theorem step_compareLeft_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (op : CmpOp) (right : Expr) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .compareLeft op right env :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .compareLeft op right env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .compareLeft op right env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have saved := inside.2 _ (List.mem_cons_self ..)
  simp only [FrameWithin] at saved
  apply Preserves.unchanged layout
  · rfl
  · refine ⟨saved, ?_⟩
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [FrameWithin] using inside.1
    · exact inside.2 frame (List.mem_cons_of_mem _ member)
  · exact step_compare_left_relocates module logical physical rename logicalAnchors physicalAnchors value op right env stack globals

theorem step_chainLeft_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (op : CmpOp) (right : Expr)
    (rest : List (CmpOp × Expr)) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .chainLeft op right rest env :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .chainLeft op right rest env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .chainLeft op right rest env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have saved := inside.2 _ (List.mem_cons_self ..)
  simp only [FrameWithin] at saved
  apply Preserves.unchanged layout
  · rfl
  · refine ⟨saved, ?_⟩
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [FrameWithin] using And.intro inside.1 saved
    · exact inside.2 frame (List.mem_cons_of_mem _ member)
  · simp only [step, relocateState, relocateWork, List.map_cons, relocateFrame, protectGenerator_next, relocateStep]

theorem step_compare_expression_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (left : Expr) (comparisons : List (CmpOp × Expr)) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.expr (.compare left comparisons) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.expr (.compare left comparisons) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.expr (.compare left comparisons) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases comparisons with
  | nil =>
    apply Preserves.unchanged layout <;>
      simp [step, protectGenerator, StepHeap, StepWithin, relocateState, relocateWork, relocateStep]
  | cons pair rest =>
    rcases pair with ⟨op, right⟩
    cases rest with
    | nil | cons =>
      apply Preserves.unchanged layout
      · rfl
      · refine ⟨inside.1, ?_⟩
        intro frame member
        rcases List.mem_cons.mp member with rfl | member
        · simpa only [FrameWithin] using inside.1
        · exact inside.2 frame member
      · simp only [step, relocateState, relocateWork, List.map_cons, relocateFrame, protectGenerator_next, relocateStep]

end FormalSW.PyAst.HeapCalls.Relocation
