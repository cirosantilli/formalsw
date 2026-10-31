import lang.py.FormalSW.AllocationIsolation
import lang.py.FormalSW.MachineAllocation
import lang.py.FormalSW.FrameIsolation

/-! Actual list and tuple steps preserve private cells and separation for their continuations. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem step_list_private (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (address : Nat) (object : Mutable.Object)
    (layout : PrivateLayout logical physical rename address object) (logicalAnchors physicalAnchors : Nat)
    (items : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (itemsInside : ∀ value ∈ items, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    let nextMap := extendMap rename logical.length physical.length
    let logicalAfter := logical ++ [Mutable.Object.list items]
    let physicalAfter := physical ++ [Mutable.Object.list (items.map (relocateValue rename))]
    step module logicalAnchors ⟨.operation .list items, stack, logical⟩ globals =
        .next ⟨.value (.ref logical.length), stack, logicalAfter⟩ ∧
      step module physicalAnchors (relocateState rename physical ⟨.operation .list items, stack, logical⟩)
          (relocateGlobals rename globals) =
        .next (relocateState nextMap physicalAfter ⟨.value (.ref logical.length), stack, logicalAfter⟩) ∧
      PrivateLayout logicalAfter physicalAfter nextMap address object ∧
      StateWithin ⟨.value (.ref logical.length), stack, logicalAfter⟩ ∧
      GlobalsWithin logicalAfter.length globals ∧
      relocateGlobals nextMap globals = relocateGlobals rename globals ∧
      (∀ address < logical.length, nextMap address = rename address) := by
  dsimp only
  obtain ⟨first, second, retained⟩ := layout.allocate_list items itemsInside
  have agree := extendMap_old rename logical.length physical.length
  have stackSame := relocateStack_congr _ rename logical.length stack agree stackInside
  have source : step module logicalAnchors ⟨.operation .list items, stack, logical⟩ globals =
      .next ⟨.value (.ref logical.length), stack, logical ++ [.list items]⟩ := by
    simp [step, primitive, result, run, first]
  refine ⟨source, ?_, retained, ?_, globalsInside.mono (by simp),
    relocateGlobals_congr _ rename logical.length globals agree globalsInside, agree⟩
  · simp only [relocateState, relocateWork, relocateRuntimeOperation, relocateOperation, step, primitive,
      result, run, second, protectGenerator_next, relocateValue, extendMap_new, stackSame]
  · exact value_state_within logical.length _ _ stack (by simp) (by simp [Mutable.Value.edge, Graph.Edge.Within]) stackInside

theorem step_tuple_private (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (privateAddress : Nat) (object : Mutable.Object)
    (layout : PrivateLayout logical physical rename privateAddress object) (nonempty : object ≠ .tuple []) (logicalAnchors physicalAnchors : Nat)
    (items : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (itemsInside : ∀ value ∈ items, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    ∃ address physicalAddress logicalAfter physicalAfter nextMap,
      step module logicalAnchors ⟨.operation .tuple items, stack, logical⟩ globals =
          .next ⟨.value (.ref address), stack, logicalAfter⟩ ∧
        step module physicalAnchors (relocateState rename physical ⟨.operation .tuple items, stack, logical⟩)
            (relocateGlobals rename globals) =
          .next (relocateState nextMap physicalAfter ⟨.value (.ref address), stack, logicalAfter⟩) ∧
        PrivateLayout logicalAfter physicalAfter nextMap privateAddress object ∧
        StateWithin ⟨.value (.ref address), stack, logicalAfter⟩ ∧
        GlobalsWithin logicalAfter.length globals ∧
        nextMap address = physicalAddress ∧
        relocateGlobals nextMap globals = relocateGlobals rename globals ∧
        (∀ old < logical.length, nextMap old = rename old) := by
  obtain ⟨address, physicalAddress, logicalAfter, physicalAfter, nextMap, first, second, retained, inside, same, agree⟩ :=
    layout.allocateTuple nonempty items itemsInside
  have larger := allocateTuple_length logical logicalAfter items (.ref address) first
  have stackSame := relocateStack_congr nextMap rename logical.length stack agree stackInside
  refine ⟨address, physicalAddress, logicalAfter, physicalAfter, nextMap, ?_, ?_, retained,
    value_state_within logical.length logicalAfter (.ref address) stack larger inside stackInside,
    globalsInside.mono larger, same,
    relocateGlobals_congr nextMap rename logical.length globals agree globalsInside, agree⟩
  · simp [step, primitive, result, run, first]
  · simp only [relocateState, relocateWork, relocateRuntimeOperation, relocateOperation, step, primitive,
      result, run, second, protectGenerator_next, relocateValue, same, stackSame]

/-- Bounds and the extended private layout suffice for the next physical write guard. -/
theorem private_state_separate (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (address : Nat) (object : Mutable.Object) (layout : PrivateLayout logical physical rename address object)
    (work : Work) (stack : List Frame) (inside : StateWithin ⟨work, stack, logical⟩) :
    Framing.StateSeparate address (relocateState rename physical ⟨work, stack, logical⟩) :=
  Framing.relocateState_separate rename physical address _ inside layout.excludes

end FormalSW.PyAst.HeapCalls.Relocation
