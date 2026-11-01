import lang.py.FormalSW.MachineBounds

/-! Allocating steps preserve suspended references while extending the address map. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

/-- Existing continuations and globals use the extended map without being rewritten at runtime. -/
theorem result_extending_relocates (rename nextMap : Nat → Nat)
    (logical physical logicalAfter physicalAfter : Mutable.Heap) (logicalAnchors physicalAnchors : Nat)
    (action otherAction : Mutable.Eval Value) (stack : List Frame) (globals : Mutable.Globals)
    (outcome : Except ExceptionObject Value)
    (agree : ∀ address < logical.length, nextMap address = rename address)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals)
    (executed : action logical = some (outcome, logicalAfter))
    (other : otherAction physical = some (outcome.map (relocateValue nextMap), physicalAfter)) :
    result (globals := relocateGlobals rename globals) physicalAnchors physical otherAction
        (stack.map (relocateFrame rename)) =
      relocateStep nextMap physicalAfter physicalAnchors
        (result (globals := globals) logicalAnchors logical action stack) := by
  rw [← relocateStack_congr nextMap rename logical.length stack agree stackInside,
    ← relocateGlobals_congr nextMap rename logical.length globals agree globalsInside]
  exact result_relocates nextMap logical physical logicalAfter physicalAfter logicalAnchors physicalAnchors
    action otherAction stack globals outcome executed other

theorem value_state_within (before : Nat) (after : Mutable.Heap) (value : Value) (stack : List Frame)
    (larger : before ≤ after.length) (inside : value.edge.Within after.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin before frame) : StateWithin ⟨.value value, stack, after⟩ :=
  ⟨inside, fun frame member => (stackInside frame member).mono larger⟩

theorem step_list_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
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
      ExecutionLayout logicalAfter physicalAfter nextMap ∧
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

/-- Interning may leave the heap unchanged; fresh tuples only append. -/
theorem allocateTuple_length (heap after : Mutable.Heap) (items : List Value) (value : Value)
    (executed : Mutable.allocateTuple items heap = some (.ok value, after)) : heap.length ≤ after.length := by
  cases items with
  | nil =>
    cases found : heap.findIdx? (fun object => decide (object = .tuple [])) with
    | none =>
      have same : heap ++ [Mutable.Object.tuple []] = after := by
        simpa [Mutable.allocateTuple, found] using congrArg (Option.map (fun pair => pair.2)) executed
      simp [← same]
    | some address =>
      have same : heap = after := by
        simpa [Mutable.allocateTuple, found] using congrArg (Option.map (fun pair => pair.2)) executed
      simp [same]
  | cons head tail =>
    have same : heap ++ [Mutable.Object.tuple (head :: tail)] = after := by
      simpa [Mutable.allocateTuple] using congrArg (Option.map (fun pair => pair.2)) executed
    simp [← same]

/-- This covers fresh tuples and empty-tuple reuse, including reuse of a private physical tuple. -/
theorem step_tuple_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
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
        ExecutionLayout logicalAfter physicalAfter nextMap ∧
        StateWithin ⟨.value (.ref address), stack, logicalAfter⟩ ∧
        GlobalsWithin logicalAfter.length globals ∧
        nextMap address = physicalAddress ∧
        relocateGlobals nextMap globals = relocateGlobals rename globals ∧
        (∀ old < logical.length, nextMap old = rename old) := by
  obtain ⟨address, physicalAddress, logicalAfter, physicalAfter, nextMap, first, second, retained, inside, same, agree⟩ :=
    layout.allocateTuple items itemsInside
  have larger := allocateTuple_length logical logicalAfter items (.ref address) first
  have stackSame := relocateStack_congr nextMap rename logical.length stack agree stackInside
  refine ⟨address, physicalAddress, logicalAfter, physicalAfter, nextMap, ?_, ?_, retained,
    value_state_within logical.length logicalAfter (.ref address) stack larger inside stackInside,
    globalsInside.mono larger, same,
    relocateGlobals_congr nextMap rename logical.length globals agree globalsInside, agree⟩
  · simp [step, primitive, result, run, first]
  · simp only [relocateState, relocateWork, relocateRuntimeOperation, relocateOperation, step, primitive,
      result, run, second, protectGenerator_next, relocateValue, same, stackSame]

end FormalSW.PyAst.HeapCalls.Relocation
