import lang.py.FormalSW.BinaryEffects
import lang.py.FormalSW.BinaryUnsupported
import lang.py.FormalSW.MachineExpressionInvariant

/-! Binary steps preserve memory layouts for success, exceptions, and unsupported dispatch. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem result_binary_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (op : BinOp) (left right : Value) (inPlace : Bool)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (leftInside : left.edge.Within logical.length) (rightInside : right.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (if inPlace then inplace op left right else Mutable.binary op left right) stack globals)
      (result physicalAnchors physical
        (if inPlace then inplace op (relocateValue rename left) (relocateValue rename right)
          else Mutable.binary op (relocateValue rename left) (relocateValue rename right))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  cases executed : (if inPlace then inplace op left right else Mutable.binary op left right) logical with
  | none =>
    have other := (layout.runtime.binary_operation_unsupported op left right inPlace leftInside rightInside).mpr executed
    apply Preserves.unchanged layout <;> simp [result, run, executed, other, StepHeap, StepWithin, relocateStep]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    obtain ⟨other, nextMap, paired, retained, agree, larger, bounded⟩ :=
      layout.binary_operation op left right inPlace leftInside rightInside outcome after executed
    have physicalGrows := HeapGrows.binary_operation op (relocateValue rename left) (relocateValue rename right)
      inPlace physical _ other paired
    exact result_preserves logical physical after other rename nextMap logicalAnchors physicalAnchors _ _ stack globals outcome
      agree larger physicalGrows retained stackInside globalsInside bounded executed paired

/-- No completion premise: unsupported dispatch and exceptional exits are covered too. -/
theorem step_binary_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (op : BinOp) (left right : Value) (inPlace : Bool)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value right, .binaryRight op left inPlace :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value right, .binaryRight op left inPlace :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value right, .binaryRight op left inPlace :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have leftInside := inside.2 _ (List.mem_cons_self ..)
  simp only [FrameWithin] at leftInside
  have stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame :=
    fun frame member => inside.2 frame (List.mem_cons_of_mem _ member)
  simpa only [step, relocateState, relocateWork, List.map_cons, relocateFrame] using
    (result_binary_preserves logical physical rename logicalAnchors physicalAnchors op left right inPlace stack globals
      layout leftInside inside.1 stackInside globalsInside).protectGenerator _ inside.2

end FormalSW.PyAst.HeapCalls.Relocation
