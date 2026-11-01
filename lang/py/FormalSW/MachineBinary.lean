import lang.py.FormalSW.SequenceArithmeticRelocation
import lang.py.FormalSW.MachineMutation

/-! Binary evaluation transports saved continuations across allocating and mutating primitives. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

/-- The primitive correspondence derives the other execution; it is not assumed to complete. -/
theorem step_binary_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (op : BinOp) (left right : Value) (inPlace : Bool)
    (stack : List Frame) (globals : Mutable.Globals)
    (leftInside : left.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals)
    (related : EvalRelocates logical physical rename
      (if inPlace then inplace op left right else Mutable.binary op left right)
      (if inPlace then inplace op (relocateValue rename left) (relocateValue rename right)
        else Mutable.binary op (relocateValue rename left) (relocateValue rename right)))
    (outcome : Except ExceptionObject Value) (after : Mutable.Heap)
    (executed : (if inPlace then inplace op left right else Mutable.binary op left right) logical = some (outcome, after)) :
    ∃ other nextMap, ExecutionLayout after other nextMap ∧
      (∀ address < logical.length, nextMap address = rename address) ∧
      GlobalsWithin after.length globals ∧
      relocateGlobals nextMap globals = relocateGlobals rename globals ∧
      step module physicalAnchors
          (relocateState rename physical ⟨.value right, .binaryRight op left inPlace :: stack, logical⟩)
          (relocateGlobals rename globals) =
        relocateStep nextMap other physicalAnchors
          (step module logicalAnchors ⟨.value right, .binaryRight op left inPlace :: stack, logical⟩ globals) ∧
      StepWithin (step module logicalAnchors ⟨.value right, .binaryRight op left inPlace :: stack, logical⟩ globals) := by
  obtain ⟨other, nextMap, paired, layout, agree, larger, bounded⟩ := related outcome after executed
  have fullStackInside : ∀ frame ∈ .binaryRight op left inPlace :: stack, FrameWithin logical.length frame := by
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [FrameWithin] using leftInside
    · exact stackInside frame member
  have transported := result_extending_relocates rename nextMap logical physical after other
    logicalAnchors physicalAnchors _ _ stack globals outcome agree stackInside globalsInside executed paired
  refine ⟨other, nextMap, layout, agree, globalsInside.mono larger,
    relocateGlobals_congr nextMap rename logical.length globals agree globalsInside, ?_, ?_⟩
  · simp only [relocateState, relocateWork, List.map_cons, relocateFrame, step]
    rw [transported]
    have sameStack := relocateStack_congr nextMap rename logical.length
      (.binaryRight op left inPlace :: stack) agree fullStackInside
    simp only [List.map_cons, relocateFrame] at sameStack
    rw [← sameStack]
    simpa only [List.map_cons, relocateFrame] using
      protectGenerator_relocates nextMap other physicalAnchors (.binaryRight op left inPlace :: stack) _
  · apply protectGenerator_within
    exact result_within logicalAnchors logical after _ stack globals outcome executed larger bounded stackInside globalsInside

end FormalSW.PyAst.HeapCalls.Relocation
