import lang.py.FormalSW.IteratorAllocatingTrace

namespace FormalSW.PyAst.IteratorCalls
open HeapCalls HeapCalls.Relocation Mutable.Relocation
set_option Elab.async false

/-- Transport the source trace and preserve every private nonempty-tuple object together.
The empty tuple may be interned and become shared, so it cannot remain excluded. -/
theorem AllocatingTrace.isolated {module : Module} {logicalAnchors : Nat} {choices : ChoiceSchedule}
    {globals : Mutable.Globals} {before after : Mutable.Heap} {first final : State}
    (trace : AllocatingTrace module logicalAnchors choices globals before first after final)
    (source : Relocation.ModuleSource module) (physical : Mutable.Heap) (rename : Nat → Nat)
    (physicalAnchors : Nat) (layout : ExecutionLayout before physical rename)
    (inside : Relocation.StateWithin before.length first)
    (globalsInside : GlobalsWithin before.length globals) :
    ∃ other nextMap, Relocation.ExtendedLayout before.length physical.length rename after other nextMap ∧
      Relocation.StateWithin after.length final ∧
      (∀ address object, object ≠ .tuple [] → PrivateLayout before physical rename address object →
        PrivateLayout after other nextMap address object) ∧
      Reaches module physicalAnchors choices (relocateGlobals rename globals)
        (Relocation.relocateState rename physical physicalAnchors first)
        (Relocation.relocateState nextMap other physicalAnchors final) := by
  induction trace generalizing physical rename with
  | @stable before after first final firstHeap finalHeap sameSize ran =>
    obtain ⟨finalHeap', other, nextMap, agree, grows, physicalGrows, finalLayout,
      heap, finalInside, _, _, reached, separated⟩ :=
      Relocation.reaches_isolated module choices logicalAnchors physicalAnchors globals source ran
        before physical rename layout firstHeap.stateHeap inside globalsInside
    have equal := finalHeap.unique heap
    subst finalHeap'
    refine ⟨other, nextMap, ⟨finalLayout, grows, physicalGrows, agree⟩, finalInside, ?_, reached⟩
    intro address object _ saved
    refine ⟨finalLayout, ?_, ?_⟩
    · have retained := (separated sameSize address saved.excludes).retains_cell object
        (Framing.relocateState_cell rename physical address physicalAnchors object _ saved.saved)
      cases final with
      | running => exact retained
      | completed outcome =>
        cases outcome with
        | ok => exact retained
        | error => exact False.elim finalHeap
    · intro index bounded
      rw [agree index (by omega)]
      exact saved.excludes index (by omega)
  | list heap items stack used resumes =>
    let nextMap := extendMap rename heap.length physical.length
    let other := physical ++ [Mutable.Object.list (items.map (relocateValue rename))]
    have agree : ∀ index < heap.length, nextMap index = rename index := extendMap_old _ _ _
    have retained := (layout.allocate_list items inside.1.2).2.2
    have stackSame := relocateStack_congr nextMap rename heap.length stack agree inside.2.1
    have resumesSame := Relocation.relocateResumes_congr nextMap rename heap.length resumes agree inside.2.2
    refine ⟨other, nextMap, ⟨retained, by simp, by simp [other], agree⟩, ?_, ?_, ?_⟩
    · exact ⟨by simp [WorkWithin, Mutable.Value.edge, Graph.Edge.Within],
        fun frame member => (inside.2.1 frame member).mono (by simp),
        fun pending member => (inside.2.2 pending member).mono (by simp)⟩
    · intro address object _ saved
      exact (saved.allocate_list items inside.1.2).2.2
    · apply Reaches.next ?_ .refl
      simp only [Relocation.relocateState, Relocation.relocateCore, HeapCalls.Relocation.relocateState,
        relocateWork, relocateRuntimeOperation, relocateOperation, relocateValue, nextMap, extendMap_new,
        stackSame, resumesSame]
      exact core_next rfl rfl
  | setAllocation heap after builtin values items stack used resumes outcome input allocated =>
    let nextMap := extendMap rename heap.length physical.length
    have agree : ∀ index < heap.length, nextMap index = rename index := extendMap_old _ _ _
    obtain ⟨other, paired, retained, size, returned⟩ := layout.allocateSetValues items (input.within layout.closed inside.1.2) outcome after allocated
    have grows : heap.length ≤ after.length := by omega
    have physicalGrows := HeapGrows.allocateSetValues _ physical _ other paired
    have stackSame := relocateStack_congr nextMap rename heap.length stack agree inside.2.1
    have resumesSame := Relocation.relocateResumes_congr nextMap rename heap.length resumes agree inside.2.2
    have globalsSame := relocateGlobals_congr nextMap rename heap.length globals agree globalsInside
    refine ⟨other, nextMap, ⟨retained, grows, physicalGrows, agree⟩,
      allocationResult_within _ _ _ _ _ _ _ returned (globalsInside.mono grows)
        (fun frame member => (inside.2.1 frame member).mono grows)
        (fun pending member => (inside.2.2 pending member).mono grows), ?_, ?_⟩
    · intro address object _ saved
      refine ⟨retained, Heapq.preserves_allocateSetValues (SavedCell address object)
        (SavedCell.allocates address object) _ physical _ other saved.saved paired, ?_⟩
      rw [size]
      exact extendMap_excludes rename heap.length physical.length address saved.excludes
        (List.getElem?_eq_some_iff.mp saved.saved).1
    · apply Reaches.next ?_ .refl
      rw [allocationResult_relocates, stackSame, resumesSame, globalsSame]
      exact setAllocation_step module physicalAnchors used choices (relocateGlobals rename globals)
        physical other builtin (values.map (relocateValue rename)) (items.map (relocateValue rename)) (stack.map (relocateFrame rename))
        (resumes.map (Relocation.relocateResume rename)) (outcome.map (relocateValue nextMap))
        (input.relocates layout inside.1.2) paired
  | bufferConstruction heap operation values bytes stack used resumes input =>
    let nextMap := extendMap rename heap.length physical.length
    let other := physical ++ [Mutable.Object.bytearray bytes]
    have agree : ∀ index < heap.length, nextMap index = rename index := extendMap_old _ _ _
    have retained := (layout.allocateBuffer bytes).2.2
    have stackSame := relocateStack_congr nextMap rename heap.length stack agree inside.2.1
    have resumesSame := Relocation.relocateResumes_congr nextMap rename heap.length resumes agree inside.2.2
    refine ⟨other, nextMap, ⟨retained, by simp, by simp [other], agree⟩, ?_, ?_, ?_⟩
    · exact ⟨by simp [WorkWithin, Mutable.Value.edge, Graph.Edge.Within],
        fun frame member => (inside.2.1 frame member).mono (by simp),
        fun pending member => (inside.2.2 pending member).mono (by simp)⟩
    · intro address object _ saved
      exact (saved.allocateBuffer bytes).2.2
    · apply Reaches.next ?_ .refl
      simp only [Relocation.relocateState, Relocation.relocateCore, HeapCalls.Relocation.relocateState,
        relocateWork, input.operation_relocates rename, relocateValue, nextMap, extendMap_new, stackSame, resumesSame]
      exact bufferAllocation_step module physicalAnchors used choices (relocateGlobals rename globals)
        physical operation (values.map (relocateValue rename)) bytes (stack.map (relocateFrame rename))
        (resumes.map (Relocation.relocateResume rename)) (input.relocates layout inside.1.2)
  | sequenceConstruction heap after operation values items asTuple address stack used resumes input allocated =>
    obtain ⟨other, nextMap, paired, retained, agree, grows, physicalGrows, bounded, kept⟩ :=
      layout.allocateSequence asTuple items (input.within layout.closed inside.1.2) address after allocated
    have stackSame := relocateStack_congr nextMap rename heap.length stack agree inside.2.1
    have resumesSame := Relocation.relocateResumes_congr nextMap rename heap.length resumes agree inside.2.2
    refine ⟨other, nextMap, ⟨retained, grows, physicalGrows, agree⟩,
      ⟨bounded, fun frame member => (inside.2.1 frame member).mono grows,
        fun pending member => (inside.2.2 pending member).mono grows⟩, kept, ?_⟩
    apply Reaches.next ?_ .refl
    simp only [Relocation.relocateState, Relocation.relocateCore, HeapCalls.Relocation.relocateState,
      relocateWork, input.operation_relocates rename, relocateValue, stackSame, resumesSame]
    exact sequenceAllocation_step module physicalAnchors used choices (relocateGlobals rename globals)
      physical other operation (values.map (relocateValue rename)) (items.map (relocateValue rename)) asTuple
      (nextMap address) (stack.map (relocateFrame rename)) (resumes.map (Relocation.relocateResume rename))
      (input.relocates layout inside.1.2) paired
  | dictionaryConstruct heap after values stack used resumes outcome arity allocated =>
    let nextMap := extendMap rename heap.length physical.length
    have agree : ∀ index < heap.length, nextMap index = rename index := extendMap_old _ _ _
    obtain ⟨other, paired, retained, size, otherSize, returned⟩ :=
      layout.dictionaryConstructAllocating values arity inside.1.2 outcome after allocated
    have grows : heap.length ≤ after.length := by omega
    have stackSame := relocateStack_congr nextMap rename heap.length stack agree inside.2.1
    have resumesSame := Relocation.relocateResumes_congr nextMap rename heap.length resumes agree inside.2.2
    have globalsSame := relocateGlobals_congr nextMap rename heap.length globals agree globalsInside
    refine ⟨other, nextMap, ⟨retained, grows, by omega, agree⟩,
      allocationResult_within _ _ _ _ _ _ _ returned (globalsInside.mono grows)
        (fun frame member => (inside.2.1 frame member).mono grows)
        (fun pending member => (inside.2.2 pending member).mono grows), ?_, ?_⟩
    · intro address object _ saved
      refine ⟨retained, Heapq.preserves_dictionaryConstruct (SavedCell address object)
        (SavedCell.allocates address object) _ physical _ other saved.saved paired, ?_⟩
      rw [size]
      exact extendMap_excludes rename heap.length physical.length address saved.excludes
        (List.getElem?_eq_some_iff.mp saved.saved).1
    · apply Reaches.next ?_ .refl
      rw [allocationResult_relocates, stackSame, resumesSame, globalsSame]
      exact dictionaryConstruct_step module physicalAnchors used choices (relocateGlobals rename globals)
        physical other (values.map (relocateValue rename)) (stack.map (relocateFrame rename))
        (resumes.map (Relocation.relocateResume rename)) (outcome.map (relocateValue nextMap)) paired
  | dictionary heap entries env stack used resumes =>
    let nextMap := extendMap rename heap.length physical.length
    let other := physical ++ [Mutable.Object.dict (entries.map fun entry => (entry.1, relocateValue rename entry.2))]
    have agree : ∀ index < heap.length, nextMap index = rename index := extendMap_old _ _ _
    have bounded : ObjectWithin heap.length (.dict entries) := by
      intro value member
      obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
      exact inside.1.2 entry present
    have retained := (layout.allocateDict entries bounded).2.2
    have stackSame := relocateStack_congr nextMap rename heap.length stack agree inside.2.1
    have resumesSame := Relocation.relocateResumes_congr nextMap rename heap.length resumes agree inside.2.2
    refine ⟨other, nextMap, ⟨retained, by simp, by simp [other], agree⟩, ?_, ?_, ?_⟩
    · exact ⟨by simp [WorkWithin, Mutable.Value.edge, Graph.Edge.Within],
        fun frame member => (inside.2.1 frame member).mono (by simp),
        fun pending member => (inside.2.2 pending member).mono (by simp)⟩
    · intro address object _ saved
      exact (saved.allocateDict entries bounded).2.2
    · apply Reaches.next ?_ .refl
      simp only [Relocation.relocateState, Relocation.relocateCore, HeapCalls.Relocation.relocateState,
        relocateWork, relocateValue, nextMap, extendMap_new, stackSame, resumesSame]
      exact core_next rfl rfl
  | tuple heap after items address stack used resumes allocated =>
    obtain ⟨left, right, logicalAfter, other, nextMap, leftRun, rightRun, retained, bounded, same, agree⟩ :=
      layout.allocateTuple items inside.1.2
    have equal : left = address ∧ logicalAfter = after := by simpa using leftRun.symm.trans allocated
    obtain ⟨equalAddress, equalHeap⟩ := equal
    subst left
    subst logicalAfter
    have grows := allocateTuple_length heap after items (.ref address) leftRun
    have physicalGrows := allocateTuple_length physical other (items.map (relocateValue rename)) (.ref right) rightRun
    have stackSame := relocateStack_congr nextMap rename heap.length stack agree inside.2.1
    have resumesSame := Relocation.relocateResumes_congr nextMap rename heap.length resumes agree inside.2.2
    refine ⟨other, nextMap, ⟨retained, grows, physicalGrows, agree⟩, ?_, ?_, ?_⟩
    · exact ⟨bounded, fun frame member => (inside.2.1 frame member).mono grows,
        fun pending member => (inside.2.2 pending member).mono grows⟩
    · intro privateAddress object nonempty saved
      refine ⟨retained, ?_, ?_⟩
      · exact Heapq.preserves_allocateTuple (SavedCell privateAddress object) (SavedCell.allocates privateAddress object)
          (items.map (relocateValue rename)) physical (.ok (.ref right)) other saved.saved rightRun
      · exact allocateTuple_map_excludes heap physical after other rename nextMap items address right privateAddress object
          leftRun rightRun same agree saved.excludes saved.saved nonempty
    · apply Reaches.next ?_ .refl
      simp only [Relocation.relocateState, Relocation.relocateCore, HeapCalls.Relocation.relocateState,
        relocateWork, relocateRuntimeOperation, relocateOperation, relocateValue, same, stackSame, resumesSame]
      apply core_next rfl
      simp [SetCalls.step, SetCalls.liftStep, HeapCalls.step, primitive, result, run, rightRun]
  | newInstance heap name origin classBody stack used resumes noFunction noLibrary defined noInitializer noDataclass =>
    let nextMap := extendMap rename heap.length physical.length
    let other := physical ++ [Mutable.Object.instance origin name []]
    have agree : ∀ index < heap.length, nextMap index = rename index := extendMap_old _ _ _
    have retained := layout.append_existing (.instance origin name []) (by simp) (by simp [ObjectWithin, objectValues])
    have stackSame := relocateStack_congr nextMap rename heap.length stack agree inside.2.1
    have resumesSame := Relocation.relocateResumes_congr nextMap rename heap.length resumes agree inside.2.2
    refine ⟨other, nextMap, ⟨retained, by simp, by simp [other], agree⟩, ?_, ?_, ?_⟩
    · exact ⟨by simp [WorkWithin, Mutable.Value.edge, Graph.Edge.Within],
        fun frame member => (inside.2.1 frame member).mono (by simp),
        fun pending member => (inside.2.2 pending member).mono (by simp)⟩
    · intro address object _ saved
      exact (saved.allocateInstance origin name).2.2
    · apply Reaches.next ?_ .refl
      simp only [Relocation.relocateState, Relocation.relocateCore, HeapCalls.Relocation.relocateState,
        relocateWork, relocateRuntimeOperation, relocateOperation, relocateValue, nextMap, extendMap_new,
        List.map_nil, stackSame, resumesSame]
      apply core_next rfl
      simp [SetCalls.step, SetCalls.liftStep, HeapCalls.step, noFunction, noLibrary,
        construct, defined, noInitializer, noDataclass, result, run, Mutable.allocateInstance_result, other]
  | initializedInstance heap name origin classBody args body values completed stack used resumes noFunction noLibrary defined initializer arguments =>
    let nextMap := extendMap rename heap.length physical.length
    let logicalAfter := heap ++ [Mutable.Object.instance origin name []]
    let other := physical ++ [Mutable.Object.instance origin name []]
    have agree : ∀ index < heap.length, nextMap index = rename index := extendMap_old _ _ _
    have larger : heap.length ≤ logicalAfter.length := by simp [logicalAfter]
    have bodySource := findFunctionIn_within 0 classBody "__init__" args body
      (findClass_within 0 module name origin classBody source defined) initializer
    have retained := layout.append_existing (.instance origin name []) (by simp) (by simp [ObjectWithin, objectValues])
    have stackSame := relocateStack_congr nextMap rename heap.length stack agree inside.2.1
    have resumesSame := Relocation.relocateResumes_congr nextMap rename heap.length resumes agree inside.2.2
    have valuesSame : values.map (relocateValue nextMap) = values.map (relocateValue rename) := by
      apply List.map_congr_left
      intro value member
      exact relocateValue_congr nextMap rename heap.length value agree (inside.1.2 value member)
    have entered : invokeMethod logicalAnchors (.ref heap.length) args body values
        (.initialized heap.length :: stack) logicalAfter globals =
        .next ⟨.block (executableBody body) (functionEnv args body completed globals),
          .initialized heap.length :: stack, logicalAfter⟩ := by
      simp [invokeMethod, arguments]
    have localInside := invokeMethod_within logicalAfter logicalAnchors (.ref heap.length) args body values
      (.initialized heap.length :: stack) globals _
      (by simp [logicalAfter, Mutable.Value.edge, Graph.Edge.Within])
      (fun value member => valueWithin_mono _ _ value larger (inside.1.2 value member))
      (fun statement member => (bodySource statement member).mono (Nat.zero_le _))
      (by intro frame member; rcases List.mem_cons.mp member with rfl | member
          · simp [FrameWithin, logicalAfter]
          · exact (inside.2.1 frame member).mono larger)
      (globalsInside.mono larger) entered
    have paired := invokeMethod_relocate nextMap logicalAfter other logicalAnchors physicalAnchors
      (.ref heap.length) args body values (.initialized heap.length :: stack) globals
    rw [entered] at paired
    have invoked : invokeMethod physicalAnchors (.ref physical.length) args body (values.map (relocateValue rename))
        (.initialized physical.length :: stack.map (relocateFrame rename)) other (relocateGlobals rename globals) =
        .next (HeapCalls.Relocation.relocateState nextMap other
          ⟨.block (executableBody body) (functionEnv args body completed globals),
            .initialized heap.length :: stack, logicalAfter⟩) := by
      simpa only [relocateValue, nextMap, extendMap_new, relocateBody_source _ body bodySource,
        List.map_cons, relocateFrame, stackSame, relocateGlobals_congr _ rename heap.length globals agree globalsInside,
        valuesSame, HeapCalls.Relocation.relocateStep] using paired
    refine ⟨other, nextMap, ⟨retained, larger, by simp [other], agree⟩,
      ⟨localInside.1, localInside.2, fun pending member => (inside.2.2 pending member).mono larger⟩, ?_, ?_⟩
    · intro address object _ saved
      exact (saved.allocateInstance origin name).2.2
    · apply Reaches.next ?_ .refl
      simp only [Relocation.relocateState, Relocation.relocateCore, resumesSame]
      apply core_next rfl
      simp only [SetCalls.step, HeapCalls.Relocation.relocateState, relocateWork, relocateRuntimeOperation,
        relocateOperation, HeapCalls.step, noFunction, noLibrary, construct, defined, initializer]
      rw [invoked]
      rfl
  | dataInstance heap name origin classBody frozen fields values stack used resumes noFunction noLibrary defined noInitializer metadata arity =>
    let declared := fields.map Arg.name
    let fresh := Mutable.Object.dataInstance origin name frozen declared (declared.zip values)
    let nextMap := extendMap rename heap.length physical.length
    let other := physical ++ [relocateObject rename fresh]
    have agree : ∀ index < heap.length, nextMap index = rename index := extendMap_old _ _ _
    have bounded : ObjectWithin heap.length fresh := by
      intro value member
      obtain ⟨pair, paired, equal⟩ := List.mem_map.mp member
      rw [← equal]
      exact inside.1.2 pair.2 (List.of_mem_zip paired).2
    have mapped : (declared.zip values).map (fun pair => (pair.1, relocateValue rename pair.2)) =
        declared.zip (values.map (relocateValue rename)) := by
      clear bounded arity inside
      induction declared generalizing values with
      | nil => rfl
      | cons field fields ih => cases values <;> simp [ih]
    have retained := layout.append_existing fresh (by simp [fresh]) bounded
    have stackSame := relocateStack_congr nextMap rename heap.length stack agree inside.2.1
    have resumesSame := Relocation.relocateResumes_congr nextMap rename heap.length resumes agree inside.2.2
    refine ⟨other, nextMap, ⟨retained, by simp, by simp [other], agree⟩, ?_, ?_, ?_⟩
    · exact ⟨by simp [WorkWithin, Mutable.Value.edge, Graph.Edge.Within],
        fun frame member => (inside.2.1 frame member).mono (by simp),
        fun pending member => (inside.2.2 pending member).mono (by simp)⟩
    · intro address object _ saved
      exact saved.append_existing fresh (by simp [fresh]) bounded
    · apply Reaches.next ?_ .refl
      simp only [Relocation.relocateState, Relocation.relocateCore, HeapCalls.Relocation.relocateState,
        relocateWork, relocateRuntimeOperation, relocateOperation, relocateValue, nextMap, extendMap_new,
        stackSame, resumesSame]
      apply core_next rfl
      simp [SetCalls.step, SetCalls.liftStep, HeapCalls.step, noFunction, noLibrary,
        construct, defined, noInitializer, metadata, result, run, Mutable.allocateDataclass_result,
        show (fields.map Arg.name).length = (values.map (relocateValue rename)).length by simpa using arity,
        other, fresh, relocateObject, mapped, declared]
  | @trans before middle after first next final left right leftIH rightIH =>
    obtain ⟨middlePhysical, middleMap, middleLayout, middleInside, firstKept, firstRan⟩ :=
      leftIH physical rename layout inside globalsInside
    obtain ⟨other, nextMap, finalLayout, finalInside, secondKept, secondRan⟩ :=
      rightIH middlePhysical middleMap middleLayout.layout middleInside (globalsInside.mono middleLayout.logicalGrows)
    refine ⟨other, nextMap, ⟨finalLayout.layout, Nat.le_trans middleLayout.logicalGrows finalLayout.logicalGrows,
      Nat.le_trans middleLayout.physicalGrows finalLayout.physicalGrows, ?_⟩, finalInside,
      fun address object nonempty saved => secondKept address object nonempty (firstKept address object nonempty saved), ?_⟩
    · intro index bounded
      exact (finalLayout.agrees index (Nat.lt_of_lt_of_le bounded middleLayout.logicalGrows)).trans
        (middleLayout.agrees index bounded)
    · have sameGlobals := relocateGlobals_congr middleMap rename before.length globals middleLayout.agrees globalsInside
      exact firstRan.trans (by simpa only [sameGlobals] using secondRan)

end FormalSW.PyAst.IteratorCalls
