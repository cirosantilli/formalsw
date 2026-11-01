import lang.py.FormalSW.MachineSliceInvariant

/-! Extending a list changes its captured receiver and preserves all element aliases. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem result_extendList_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (address : Nat) (source : Value)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (addressInside : address < logical.length) (sourceInside : source.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (primitive (.extendList address) [source]) stack globals)
      (result physicalAnchors physical (primitive (.extendList (rename address)) [relocateValue rename source])
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem addressInside
  have moved := layout.runtime.lookup address _ found
  cases object : logical[address] <;> simp only [object, relocateObject] at moved
  case list items =>
    cases source with
    | scalar scalar =>
      apply Preserves.unchanged layout <;>
        simp [result, run, primitive, extendList, found, object, moved, relocateValue,
          Mutable.unsupported, StepHeap, StepWithin, relocateStep]
    | ref other =>
      have input : logical[other]? = some logical[other] := List.getElem?_eq_getElem sourceInside
      have inputMoved := layout.runtime.lookup other _ input
      cases inputObject : logical[other] <;> simp only [inputObject, relocateObject] at inputMoved
      case list additional | tuple additional =>
        have boundedItems := layout.closed (.list items) (List.mem_of_getElem? (found.trans (congrArg some object)))
        have boundedAdditional := layout.closed _ (List.mem_of_getElem? (input.trans (congrArg some inputObject)))
        have bounded : ObjectWithin logical.length (.list (items ++ additional)) := by
          intro value member
          exact (List.mem_append.mp member).elim (boundedItems value) (boundedAdditional value)
        have preserved := result_storeSliceObject_preserves logical physical rename logicalAnchors physicalAnchors
          address (.list items) (.list (items ++ additional)) stack globals layout
          (found.trans (congrArg some object)) (by simp) (by simp) bounded stackInside globalsInside
        simpa [result, run, primitive, extendList, found, object, moved, input, inputObject, inputMoved,
          relocateValue, relocateObject, List.map_append, storeSliceObject, Mutable.eval_bind, Except.map] using preserved
      all_goals
        apply Preserves.unchanged layout <;>
          simp [result, run, primitive, extendList, found, object, moved, input, inputObject, inputMoved,
            relocateValue, Mutable.unsupported, StepHeap, StepWithin, relocateStep]
  all_goals
    apply Preserves.unchanged layout <;>
      simp [result, run, primitive, extendList, found, object, moved,
        Mutable.unsupported, StepHeap, StepWithin, relocateStep]

end FormalSW.PyAst.HeapCalls.Relocation
