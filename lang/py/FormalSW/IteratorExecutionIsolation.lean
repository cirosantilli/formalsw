import lang.py.FormalSW.IteratorOperationRelocation
import lang.py.FormalSW.IteratorFrameComposition
import lang.py.FormalSW.AllocationIsolation

/-! Complete method executions that do not grow the logical heap preserve every private cell. -/
namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation
set_option Elab.async false

/-- Transport the actual trace; unchanged heap size makes every intermediate address map retain its original domain. -/
theorem reaches_isolated (module : Module) (choices : ChoiceSchedule)
    (logicalAnchors physicalAnchors : Nat) (globals : Mutable.Globals) (source : ModuleSource module)
    {first final : State} (before : Reaches module logicalAnchors choices globals first final)
    (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout logical physical rename) (heap : StateHeap logical first)
    (inside : StateWithin logical.length first) (globalsInside : GlobalsWithin logical.length globals) :
    ∃ after other nextMap,
      (∀ address < logical.length, nextMap address = rename address) ∧
      logical.length ≤ after.length ∧ physical.length ≤ other.length ∧
      ExecutionLayout after other nextMap ∧ StateHeap after final ∧
      StateWithin after.length final ∧ GlobalsWithin after.length globals ∧
      relocateGlobals nextMap globals = relocateGlobals rename globals ∧
      Reaches module physicalAnchors choices (relocateGlobals rename globals)
        (relocateState rename physical physicalAnchors first) (relocateState nextMap other physicalAnchors final) ∧
      (after.length = logical.length → ∀ address,
        (∀ index < logical.length, rename index ≠ address) →
        Framing.SeparatedReaches module physicalAnchors address choices (relocateGlobals rename globals)
          (relocateState rename physical physicalAnchors first) (relocateState nextMap other physicalAnchors final)) := by
  induction before generalizing logical physical rename with
  | refl =>
      exact ⟨logical, physical, rename, fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _,
        layout, heap, inside, globalsInside, rfl, .refl, fun _ _ _ => .refl⟩
  | @next state following final transition before ih =>
      have preserved := step_complete_preserves module choices state logical physical rename
        logicalAnchors physicalAnchors globals source layout heap inside globalsInside
      rw [transition] at preserved
      obtain ⟨middle, middlePhysical, middleMap, agree, grows, physicalGrows, middleLayout,
        middleHeap, middleInside, middleGlobals, sameGlobals, moved⟩ := preserved.next globals globalsInside
      obtain ⟨after, other, nextMap, nextAgree, nextGrows, nextPhysicalGrows, finalLayout,
        finalHeap, finalInside, finalGlobals, finalSameGlobals, reached, separated⟩ :=
        ih middle middlePhysical middleMap middleLayout middleHeap middleInside middleGlobals
      refine ⟨after, other, nextMap, ?_, Nat.le_trans grows nextGrows,
        Nat.le_trans physicalGrows nextPhysicalGrows, finalLayout, finalHeap, finalInside, finalGlobals,
        finalSameGlobals.trans sameGlobals, ?_, ?_⟩
      · intro address bounded
        exact (nextAgree address (Nat.lt_of_lt_of_le bounded grows)).trans (agree address bounded)
      · exact .next moved (by simpa only [sameGlobals] using reached)
      · intro noGrowth address outside
        have middleSize : middle.length = logical.length := by omega
        have finalSize : after.length = middle.length := noGrowth.trans middleSize.symm
        have nextOutside : ∀ index < middle.length, middleMap index ≠ address := by
          intro index bounded
          have old : index < logical.length := by omega
          rw [agree index old]
          exact outside index old
        exact .next (Framing.relocateState_separate rename logical physical address physicalAnchors
          state heap inside outside) moved (by simpa only [sameGlobals] using separated finalSize address nextOutside)

/-- One transported execution retains all excluded cells simultaneously, including under saved consumers. -/
theorem operation_completion_isolated (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used finalUsed : Nat)
    (operation : Operation) (outcome : Except ExceptionObject Mutable.Value) (after : Mutable.Heap)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (inside : OperationWithin logical.length operation) (globalsInside : GlobalsWithin logical.length globals)
    (executed : Reaches module logicalAnchors choices globals
      (.running ⟨⟨.operation operation [], [], logical⟩, used⟩ [])
      (.completed (.ok ⟨outcome, globals, after, logicalAnchors⟩) finalUsed []))
    (noGrowth : after.length = logical.length) :
    ∃ other nextMap, ExtendedLayout logical.length physical.length rename after other nextMap ∧
      (∀ address object, PrivateLayout logical physical rename address object →
        PrivateLayout after other nextMap address object) ∧
      ∀ resumes, Reaches module physicalAnchors choices (relocateGlobals rename globals)
        (.running ⟨⟨.operation (relocateRuntimeOperation rename operation) [], [], physical⟩, used⟩ resumes)
        (.completed (.ok (relocateCompletion nextMap other physicalAnchors
          ⟨outcome, globals, after, logicalAnchors⟩)) finalUsed resumes) := by
  obtain ⟨finalHeap, other, nextMap, agree, grows, physicalGrows, finalLayout, finalStateHeap,
    _, _, _, reached, separated⟩ := reaches_isolated module choices logicalAnchors physicalAnchors
      globals source executed logical physical rename layout rfl
      ⟨⟨inside, by simp⟩, by simp, by simp⟩ globalsInside
  have equal : after = finalHeap := finalStateHeap
  subst finalHeap
  refine ⟨other, nextMap, ⟨finalLayout, grows, physicalGrows, agree⟩, ?_, ?_⟩
  · intro address object privateLayout
    refine ⟨finalLayout, ?_, ?_⟩
    · exact (separated noGrowth address privateLayout.excludes).retains_cell object
        (Framing.relocateState_cell rename physical address physicalAnchors object _ privateLayout.saved)
    · intro index bounded
      have old : index < logical.length := by omega
      rw [agree index old]
      exact privateLayout.excludes index old
  · intro resumes
    simpa only [relocateState, relocateCore, HeapCalls.Relocation.relocateState, relocateWork,
      List.map_nil, Except.map, appendResumes, List.nil_append] using reached.append_resumes resumes

/-- Advancing any suspended consumer uses the same isolated method execution and resulting heap. -/
theorem advance_completion_isolated (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used finalUsed : Nat)
    (iterator : Mutable.Value) (operation : Operation) (outcome : Except ExceptionObject Mutable.Value)
    (after : Mutable.Heap) (globals : Mutable.Globals) (source : ModuleSource module)
    (layout : ExecutionLayout logical physical rename) (inside : iterator.edge.Within logical.length)
    (globalsInside : GlobalsWithin logical.length globals)
    (isObject : isInstance logical iterator = true)
    (bound : ProtocolCalls.nextMethod module iterator logical = some (.ok (some operation), logical))
    (executed : Reaches module logicalAnchors choices globals
      (.running ⟨⟨.operation operation [], [], logical⟩, used⟩ [])
      (.completed (.ok ⟨outcome, globals, after, logicalAnchors⟩) finalUsed []))
    (noGrowth : after.length = logical.length) :
    ∃ other nextMap, ExtendedLayout logical.length physical.length rename after other nextMap ∧
      (∀ address object, PrivateLayout logical physical rename address object →
        PrivateLayout after other nextMap address object) ∧
      ∀ loop resumes, Reaches module physicalAnchors choices (relocateGlobals rename globals)
        (.running ⟨⟨.block (loopCode loop (relocateValue rename iterator) :: loop.following) loop.env,
          loop.stack, physical⟩, used⟩ resumes)
        (.completed (.ok ⟨outcome.map (relocateValue nextMap), relocateGlobals rename globals, other, physicalAnchors⟩)
          finalUsed (.advance loop (relocateValue rename iterator) :: resumes)) := by
  have method := nextMethod_source module iterator logical logical operation source bound
  obtain ⟨other, nextMap, extended, kept, called⟩ := operation_completion_isolated module choices logical physical rename
    logicalAnchors physicalAnchors used finalUsed operation outcome after globals source layout
    (method.within logical.length inside) globalsInside executed noGrowth
  have moved := nextMethod_runtime_relocates layout.runtime module iterator source inside
  rw [bound] at moved
  simp only [Option.map, Except.map] at moved
  have instanceMoved : isInstance physical (relocateValue rename iterator) = true :=
    (isInstance_relocates layout.runtime iterator inside).trans isObject
  have sameGlobals : relocateGlobals nextMap globals = relocateGlobals rename globals :=
    relocateGlobals_congr nextMap rename logical.length globals extended.agrees globalsInside
  refine ⟨other, nextMap, extended, kept, fun loop resumes => ?_⟩
  apply Reaches.next (following := .running
    ⟨⟨.operation (relocateRuntimeOperation rename operation) [], [], physical⟩, used⟩
      (.advance loop (relocateValue rename iterator) :: resumes))
  · simp [step, intercept, loopCode, instanceMoved, enter, moved]
  · simpa only [relocateCompletion, sameGlobals] using called (.advance loop (relocateValue rename iterator) :: resumes)

end FormalSW.PyAst.IteratorCalls.Relocation
