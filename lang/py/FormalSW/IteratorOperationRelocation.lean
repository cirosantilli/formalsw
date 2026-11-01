import lang.py.FormalSW.IteratorExecutionRelocation
import lang.py.FormalSW.IteratorContinuation

/-! Derive a protocol call in the physical heap from its logical execution alone. -/
namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation
set_option Elab.async false

/-- Saved physical callers need not be images of logical callers: attach them only after transport. -/
theorem operation_completion_relocates (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used finalUsed : Nat)
    (operation : Operation) (outcome : Except ExceptionObject Mutable.Value) (after : Mutable.Heap)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (inside : OperationWithin logical.length operation) (globalsInside : GlobalsWithin logical.length globals)
    (executed : Reaches module logicalAnchors choices globals
      (.running ⟨⟨.operation operation [], [], logical⟩, used⟩ [])
      (.completed (.ok ⟨outcome, globals, after, logicalAnchors⟩) finalUsed [])) :
    ∃ other nextMap, ExtendedLayout logical.length physical.length rename after other nextMap ∧
      ∀ resumes, Reaches module physicalAnchors choices (relocateGlobals rename globals)
        (.running ⟨⟨.operation (relocateRuntimeOperation rename operation) [], [], physical⟩, used⟩ resumes)
        (.completed (.ok (relocateCompletion nextMap other physicalAnchors
          ⟨outcome, globals, after, logicalAnchors⟩)) finalUsed resumes) := by
  have related : ExecutionStates logical.length physical.length rename physicalAnchors globals
      (relocateGlobals rename globals) (.running ⟨⟨.operation operation [], [], logical⟩, used⟩ [])
      (relocateState rename physical physicalAnchors (.running ⟨⟨.operation operation [], [], logical⟩, used⟩ [])) :=
    ⟨logical, physical, rename, ⟨layout, Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl⟩,
      rfl, ⟨⟨inside, by simp⟩, by simp, by simp⟩, globalsInside, rfl, rfl⟩
  obtain ⟨otherFinal, paired, reached⟩ := reaches_relocates module choices logical.length physical.length rename
    logicalAnchors physicalAnchors globals (relocateGlobals rename globals) source _ _ _ related executed
  obtain ⟨finalHeap, other, nextMap, extended, heap, _, _, _, same⟩ := paired
  have equal : after = finalHeap := heap
  subst finalHeap
  refine ⟨other, nextMap, extended, fun resumes => ?_⟩
  rw [same] at reached
  simpa only [relocateState, relocateCore, HeapCalls.Relocation.relocateState, relocateWork,
    List.map_nil, Except.map, appendResumes, List.nil_append] using reached.append_resumes resumes

/-- Derive advancement in a different consumer without assuming its method execution. -/
theorem advance_completion_relocates (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used finalUsed : Nat)
    (iterator : Mutable.Value) (operation : Operation) (outcome : Except ExceptionObject Mutable.Value)
    (after : Mutable.Heap) (globals : Mutable.Globals) (source : ModuleSource module)
    (layout : ExecutionLayout logical physical rename) (inside : iterator.edge.Within logical.length)
    (globalsInside : GlobalsWithin logical.length globals)
    (isObject : isInstance logical iterator = true)
    (bound : ProtocolCalls.nextMethod module iterator logical = some (.ok (some operation), logical))
    (executed : Reaches module logicalAnchors choices globals
      (.running ⟨⟨.operation operation [], [], logical⟩, used⟩ [])
      (.completed (.ok ⟨outcome, globals, after, logicalAnchors⟩) finalUsed [])) :
    ∃ other nextMap, ExtendedLayout logical.length physical.length rename after other nextMap ∧
      ∀ loop resumes, Reaches module physicalAnchors choices (relocateGlobals rename globals)
        (.running ⟨⟨.block (loopCode loop (relocateValue rename iterator) :: loop.following) loop.env,
          loop.stack, physical⟩, used⟩ resumes)
        (.completed (.ok ⟨outcome.map (relocateValue nextMap), relocateGlobals rename globals, other, physicalAnchors⟩)
          finalUsed (.advance loop (relocateValue rename iterator) :: resumes)) := by
  have method := nextMethod_source module iterator logical logical operation source bound
  obtain ⟨other, nextMap, extended, called⟩ := operation_completion_relocates module choices logical physical rename
    logicalAnchors physicalAnchors used finalUsed operation outcome after globals source layout
    (method.within logical.length inside) globalsInside executed
  have moved := nextMethod_runtime_relocates layout.runtime module iterator source inside
  rw [bound] at moved
  simp only [Option.map, Except.map] at moved
  have instanceMoved : isInstance physical (relocateValue rename iterator) = true :=
    (isInstance_relocates layout.runtime iterator inside).trans isObject
  have sameGlobals : relocateGlobals nextMap globals = relocateGlobals rename globals :=
    relocateGlobals_congr nextMap rename logical.length globals extended.agrees globalsInside
  refine ⟨other, nextMap, extended, fun loop resumes => ?_⟩
  apply Reaches.next (following := .running
    ⟨⟨.operation (relocateRuntimeOperation rename operation) [], [], physical⟩, used⟩
      (.advance loop (relocateValue rename iterator) :: resumes))
  · simp [step, intercept, loopCode, instanceMoved, enter, moved]
  · simpa only [relocateCompletion, sameGlobals] using
      called (.advance loop (relocateValue rename iterator) :: resumes)

end FormalSW.PyAst.IteratorCalls.Relocation
