import lang.py.FormalSW.MachineZip
import lang.py.FormalSW.DictionaryItemsCalls

/-! Dictionary cursors retain keys while reading current shared values. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem dictionaryItemFields_relocates (rename : Nat → Nat) (object : Mutable.Object) :
    dictionaryItemFields (relocateObject rename object) =
      (dictionaryItemFields object).map (List.map (relocatePair rename)) := by
  cases object <;> simp [dictionaryItemFields, relocateObject, relocatePair, relocateValue, List.map_map, Function.comp_def]

theorem dictionaryItemFields_within (limit : Nat) (object : Mutable.Object) (entries : List (Value × Value))
    (inside : ObjectWithin limit object) (fields : dictionaryItemFields object = some entries) :
    ∀ entry ∈ entries, entry.1.edge.Within limit ∧ entry.2.edge.Within limit := by
  cases object <;> simp only [dictionaryItemFields] at fields <;> try contradiction
  case dict values =>
    cases fields
    intro entry member
    obtain ⟨pair, present, rfl⟩ := List.mem_map.mp member
    exact ⟨True.intro, inside pair.2 (List.mem_map.mpr ⟨pair, present, rfl⟩)⟩
  case keyDict values =>
    cases fields
    intro entry member
    obtain ⟨pair, present, rfl⟩ := List.mem_map.mp member
    exact ⟨inside pair.2.1 (List.mem_flatMap.mpr ⟨pair, present, by simp⟩),
      inside pair.2.2 (List.mem_flatMap.mpr ⟨pair, present, by simp⟩)⟩

theorem relocateSource_eq_iff (rename : Nat → Nat) (limit : Nat)
    (injective : Graph.Relocation.InjectiveBelow rename limit) (left right : SequenceSource)
    (leftInside : SourceWithin limit left) (rightInside : SourceWithin limit right) :
    relocateSource rename left = relocateSource rename right ↔ left = right := by
  cases left with
  | scalar value => cases right <;> simp [relocateSource]
  | ref address =>
    cases right with
    | scalar value => simp [relocateSource]
    | ref other =>
      simp only [relocateSource, SequenceSource.ref.injEq]
      exact ⟨injective address leftInside other rightInside, congrArg rename⟩

theorem relocateSources_eq_iff (rename : Nat → Nat) (limit : Nat)
    (injective : Graph.Relocation.InjectiveBelow rename limit) (left right : List SequenceSource)
    (leftInside : ∀ source ∈ left, SourceWithin limit source)
    (rightInside : ∀ source ∈ right, SourceWithin limit source) :
    left.map (relocateSource rename) = right.map (relocateSource rename) ↔ left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp
  | cons source rest ih =>
    cases right with
    | nil => simp
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq]
      rw [relocateSource_eq_iff rename limit injective source other
        (leftInside source (by simp)) (rightInside other (by simp)),
        ih tail (fun item member => leftInside item (by simp [member]))
          (fun item member => rightInside item (by simp [member]))]

theorem dictionaryKeys_relocate (rename : Nat → Nat) (entries : List (Value × Value)) :
    ((entries.map (relocatePair rename)).map fun entry => sequenceSource entry.1) =
      (entries.map fun entry => sequenceSource entry.1).map (relocateSource rename) := by
  simp only [List.map_map, Function.comp_def, relocatePair, sequenceSource_relocate]

theorem dictionaryItemsNext_keeps_heap (heap : Mutable.Heap) (address : Nat) (keys : List SequenceSource)
    (position : Nat) (outcome : Except ExceptionObject (Option (Value × Value))) (after : Mutable.Heap)
    (executed : dictionaryItemsNext address keys position heap = some (outcome, after)) : after = heap := by
  cases found : heap[address]? with
  | none => simp [dictionaryItemsNext, found, Mutable.unsupported] at executed
  | some object =>
    cases fields : dictionaryItemFields object with
    | none => simp [dictionaryItemsNext, found, fields, Mutable.unsupported] at executed
    | some entries =>
      by_cases size : entries.length = keys.length
      · by_cases same : entries.map (fun entry => sequenceSource entry.1) = keys
        · simpa [dictionaryItemsNext, found, fields, size, same] using (congrArg (Option.map Prod.snd) executed).symm
        · simp [dictionaryItemsNext, found, fields, size, same, Mutable.unsupported] at executed
      · simpa [dictionaryItemsNext, found, fields, size, Mutable.error] using (congrArg (Option.map Prod.snd) executed).symm

theorem dictionaryItemsNext_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (address : Nat) (keys : List SequenceSource) (position : Nat)
    (addressInside : address < logical.length) (keysInside : ∀ key ∈ keys, SourceWithin logical.length key) :
    dictionaryItemsNext (rename address) (keys.map (relocateSource rename)) position physical =
      (dictionaryItemsNext address keys position logical).map
        (fun pair => (pair.1.map (Option.map (relocatePair rename)), physical)) := by
  have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem addressInside
  have moved := layout.lookup address _ found
  cases fields : dictionaryItemFields logical[address] with
  | none => simp [dictionaryItemsNext, moved, found, dictionaryItemFields_relocates, fields, Mutable.unsupported]
  | some entries =>
    have bounded := dictionaryItemFields_within logical.length logical[address] entries
      (closed logical[address] (List.mem_of_getElem? found)) fields
    have keysBounded : ∀ key ∈ entries.map (fun entry => sequenceSource entry.1), SourceWithin logical.length key := by
      intro key member
      obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
      exact sequenceSource_within logical.length entry.1 (bounded entry present).1
    have same := relocateSources_eq_iff rename logical.length layout.injective
      (entries.map fun entry => sequenceSource entry.1) keys keysBounded keysInside
    simp only [List.map_map, Function.comp_def] at same
    by_cases size : entries.length = keys.length <;>
      simp [dictionaryItemsNext, moved, found, dictionaryItemFields_relocates, fields,
        List.map_map, Function.comp_def, relocatePair, sequenceSource_relocate,
        size, same, Mutable.error, Except.map, List.getElem?_map]
    split <;> simp [Mutable.unsupported]

theorem dictionaryItemsNext_values_within (heap : Mutable.Heap) (closed : Closed heap)
    (address : Nat) (keys : List SequenceSource) (position : Nat) (key value : Value)
    (executed : dictionaryItemsNext address keys position heap = some (.ok (some (key, value)), heap)) :
    key.edge.Within heap.length ∧ value.edge.Within heap.length := by
  cases found : heap[address]? with
  | none => simp [dictionaryItemsNext, found, Mutable.unsupported] at executed
  | some object =>
    cases fields : dictionaryItemFields object with
    | none => simp [dictionaryItemsNext, found, fields, Mutable.unsupported] at executed
    | some entries =>
      by_cases size : entries.length = keys.length
      · by_cases same : entries.map (fun entry => sequenceSource entry.1) = keys
        · have item : entries[position]? = some (key, value) := by
            simpa [dictionaryItemsNext, found, fields, size, same] using executed
          exact dictionaryItemFields_within heap.length object entries (closed object (List.mem_of_getElem? found)) fields
            (key, value) (List.mem_of_getElem? item)
        · simp [dictionaryItemsNext, found, fields, size, same, Mutable.unsupported] at executed
      · simp [dictionaryItemsNext, found, fields, size, Mutable.error] at executed

theorem dictionaryValuesBody_relocates (rename : Nat → Nat) (target : Expr) (body : List Stmt) :
    dictionaryValuesBody target (body.map (relocateStmt rename)) =
      (dictionaryValuesBody target body).map (relocateStmt rename) := by
  simp [dictionaryValuesBody, relocateStmt]

theorem dictionaryItemsStart_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
    (target : Expr) (receiver : Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (inside : receiver.edge.Within logical.length) :
    dictionaryItemsStart physicalAnchors target (body.map (relocateStmt rename))
        (otherwise.map (relocateStmt rename)) (following.map (relocateStmt rename))
        (relocateEnv rename env) (relocateValue rename receiver) (stack.map (relocateFrame rename)) physical
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (dictionaryItemsStart logicalAnchors target body otherwise following env receiver stack logical globals) := by
  cases receiver with
  | scalar value => simp [dictionaryItemsStart, relocateValue, done, relocateStep, relocateCompletion, Except.map]
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    simp only [relocateValue]
    cases object : logical[address] <;>
      simp [dictionaryItemsStart, moved, found, object, relocateObject, dictionaryItemFields,
        relocateStep, relocateState, relocateWork, relocateStmt, done, relocateCompletion, Except.map,
        List.map_map, Function.comp_def, sequenceSource_relocate, comprehensionTargetBody_relocates]
    case dict => intros; rfl
    all_goals
      split <;> simp_all only [List.map_cons, relocateFrame, relocateValue]
      all_goals split <;> simp_all only [List.map_cons, relocateFrame]

theorem dictionaryValuesStart_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
    (target : Expr) (receiver : Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (inside : receiver.edge.Within logical.length) :
    dictionaryValuesStart physicalAnchors target (body.map (relocateStmt rename))
        (otherwise.map (relocateStmt rename)) (following.map (relocateStmt rename))
        (relocateEnv rename env) (relocateValue rename receiver) (stack.map (relocateFrame rename)) physical
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (dictionaryValuesStart logicalAnchors target body otherwise following env receiver stack logical globals) := by
  cases receiver with
  | scalar value => simp [dictionaryValuesStart, relocateValue, done, relocateStep, relocateCompletion, Except.map]
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    simp only [relocateValue]
    cases object : logical[address] <;>
      simp [dictionaryValuesStart, moved, found, object, relocateObject, dictionaryItemFields,
        relocateStep, relocateState, relocateWork, relocateStmt, done, relocateCompletion, Except.map,
        List.map_map, Function.comp_def, sequenceSource_relocate, dictionaryValuesBody_relocates]
    case dict => intros; rfl
    all_goals
      split <;> simp_all only [List.map_cons, relocateFrame, relocateValue]
      all_goals split <;> simp_all only [List.map_cons, relocateFrame]

variable (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
  (logicalAnchors physicalAnchors : Nat)

theorem step_dictionary_items_start_relocates (layout : RuntimeLayout logical physical rename)
    (target : Expr) (receiver : Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (inside : receiver.edge.Within logical.length) :
    step module physicalAnchors
        (relocateState rename physical ⟨.value receiver, .dictionaryItemsReceiver target body otherwise following env :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value receiver, .dictionaryItemsReceiver target body otherwise following env :: stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateFrame, step]
  rw [← protectGenerator_relocates]
  simp only [List.map_cons, relocateFrame]
  congr 1
  exact dictionaryItemsStart_relocates logical physical rename layout logicalAnchors physicalAnchors
    target receiver body otherwise following env stack globals inside

theorem step_dictionary_values_start_relocates (layout : RuntimeLayout logical physical rename)
    (target : Expr) (receiver : Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (inside : receiver.edge.Within logical.length) :
    step module physicalAnchors
        (relocateState rename physical ⟨.value receiver, .dictionaryValuesReceiver target body otherwise following env :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value receiver, .dictionaryValuesReceiver target body otherwise following env :: stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateFrame, step]
  rw [← protectGenerator_relocates]
  simp only [List.map_cons, relocateFrame]
  congr 1
  exact dictionaryValuesStart_relocates logical physical rename layout logicalAnchors physicalAnchors
    target receiver body otherwise following env stack globals inside

/-- Each successful row allocates a tuple; stopped reads retain the old layout. -/
theorem step_dictionary_items_loop_relocates (layout : ExecutionLayout logical physical rename)
    (name : String) (address : Nat) (keys : List SequenceSource) (position : Nat) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (globalsInside : GlobalsWithin logical.length globals)
    (inside : StateWithin ⟨.block (.dictionaryItemsStepLoop name address keys position body otherwise :: following) env, stack, logical⟩) :
    ∃ after other nextMap, ExecutionLayout after other nextMap ∧
      logical.length ≤ after.length ∧ (∀ address < logical.length, nextMap address = rename address) ∧
      GlobalsWithin after.length globals ∧ relocateGlobals nextMap globals = relocateGlobals rename globals ∧
      step module physicalAnchors
          (relocateState rename physical ⟨.block (.dictionaryItemsStepLoop name address keys position body otherwise :: following) env, stack, logical⟩)
          (relocateGlobals rename globals) =
        relocateStep nextMap other physicalAnchors
          (step module logicalAnchors ⟨.block (.dictionaryItemsStepLoop name address keys position body otherwise :: following) env, stack, logical⟩ globals) ∧
      StepWithin (step module logicalAnchors ⟨.block (.dictionaryItemsStepLoop name address keys position body otherwise :: following) env, stack, logical⟩ globals) := by
  have loopInside := inside.1.2 _ (List.mem_cons_self ..)
  have restInside : ∀ statement ∈ following, StmtWithin logical.length statement :=
    fun statement member => inside.1.2 statement (by simp [member])
  have nextInside := loopContinuation_within logical.length body
    (.dictionaryItemsStepLoop name address keys (position + 1) body otherwise) (by simpa only [StmtWithin] using loopInside)
  simp only [StmtWithin] at loopInside
  have paired := dictionaryItemsNext_relocates layout.runtime layout.closed address keys position loopInside.1 loopInside.2.1
  cases fetched : dictionaryItemsNext address keys position logical with
  | none =>
    refine ⟨logical, physical, rename, layout, Nat.le_refl _, fun _ _ => rfl, globalsInside, rfl, ?_, ?_⟩
    · simp [relocateState, relocateWork, relocateStmt, step, run, paired, fetched, relocateStep]
    · simp [step, run, fetched, StepWithin, protectGenerator]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have unchanged := dictionaryItemsNext_keeps_heap logical address keys position outcome after fetched
    subst after
    cases outcome with
    | error exception =>
      refine ⟨logical, physical, rename, layout, Nat.le_refl _, fun _ _ => rfl, globalsInside, rfl, ?_, ?_⟩
      · simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step]
        rw [← protectGenerator_relocates]
        congr 1
        simp [run, paired, fetched, done, relocateStep, relocateCompletion, Except.map]
      · apply protectGenerator_within
        simp only [run, fetched, done]
        exact ⟨globalsInside, by intro value impossible; cases impossible⟩
    | ok fields =>
      cases fields with
      | none =>
        refine ⟨logical, physical, rename, layout, Nat.le_refl _, fun _ _ => rfl, globalsInside, rfl, ?_, ?_⟩
        · simp [relocateState, relocateWork, relocateStmt, step, run, paired, fetched, relocateStep, Except.map]
        · simp only [step, run, fetched, protectGenerator_next]
          exact ⟨⟨inside.1.1, by
            simpa only [List.mem_append, or_imp, forall_and]
              using And.intro loopInside.2.2.2 restInside⟩, inside.2⟩
      | some pair =>
        rcases pair with ⟨key, value⟩
        have fieldsInside := dictionaryItemsNext_values_within logical layout.closed address keys position key value fetched
        obtain ⟨tupleAddress, physicalAddress, after, other, nextMap, first, second, retained, bounded, same, agree⟩ :=
          layout.allocateTuple [key, value] (by simpa using fieldsInside)
        simp only [List.map_cons, List.map_nil] at second
        have larger := allocateTuple_length logical after [key, value] (.ref tupleAddress) first
        have statementsInside : ∀ statement ∈ body ++ [Calls.loopContinuation body
            (.dictionaryItemsStepLoop name address keys (position + 1) body otherwise)] ++ following,
            StmtWithin logical.length statement := by
          simpa only [List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq]
            using And.intro (And.intro loopInside.2.2.1 nextInside) restInside
        have envSame := relocateEnv_congr nextMap rename logical.length env agree inside.1.1
        have stackSame := relocateStack_congr nextMap rename logical.length stack agree inside.2
        have statementsSame := List.map_congr_left (fun statement member =>
          relocateStmt_congr nextMap rename logical.length statement agree (statementsInside statement member))
        refine ⟨after, other, nextMap, retained, larger, agree, globalsInside.mono larger,
          relocateGlobals_congr nextMap rename logical.length globals agree globalsInside, ?_, ?_⟩
        · simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step, run, paired, fetched,
            Option.map_some, Except.map, relocatePair, first, second, protectGenerator_next, relocateStep]
          simp only [relocateEnv_set, relocateValue, same, envSame, stackSame]
          rw [statementsSame]
          simp only [List.map_append, List.map_cons, List.map_nil, ← loopContinuation_relocate, relocateStmt]
        · simp only [step, run, fetched, first, protectGenerator_next]
          exact ⟨⟨(inside.1.1.mono larger).setLocal name (.ref tupleAddress) bounded,
            fun statement member => (statementsInside statement member).mono larger⟩,
            fun frame member => (inside.2 frame member).mono larger⟩

theorem dictionaryValuesBody_within (limit : Nat) (target : Expr) (body : List Stmt)
    (inside : ∀ statement ∈ body, StmtWithin limit statement) :
    ∀ statement ∈ dictionaryValuesBody target body, StmtWithin limit statement := by
  simpa [dictionaryValuesBody, StmtWithin] using inside

theorem step_for_dictionary_items_relocates (target receiver : Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.block (.forDictionaryItems target receiver body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.block (.forDictionaryItems target receiver body otherwise :: following) env, stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step, protectGenerator_next, relocateStep, relocateFrame]

theorem StateWithin.for_dictionary_items (heap : Mutable.Heap) (anchors : Nat)
    (target receiver : Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin ⟨.block (.forDictionaryItems target receiver body otherwise :: following) env, stack, heap⟩) :
    StepWithin (step module anchors ⟨.block (.forDictionaryItems target receiver body otherwise :: following) env, stack, heap⟩ globals) := by
  have loopInside := inside.1.2 _ (List.mem_cons_self ..)
  simp only [StmtWithin] at loopInside
  refine ⟨inside.1.1, ?_⟩
  intro frame member
  rcases List.mem_cons.mp member with rfl | member
  · simp only [FrameWithin]
    exact ⟨inside.1.1, loopInside.1, loopInside.2, fun statement member => inside.1.2 statement (by simp [member])⟩
  · exact inside.2 frame member

theorem step_for_dictionary_values_relocates (target receiver : Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.block (.forIn target (.dictionaryValuesIterable receiver) body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.block (.forIn target (.dictionaryValuesIterable receiver) body otherwise :: following) env, stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step, protectGenerator_next, relocateStep, relocateFrame]

theorem StateWithin.for_dictionary_values (heap : Mutable.Heap) (anchors : Nat)
    (target receiver : Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin ⟨.block (.forIn target (.dictionaryValuesIterable receiver) body otherwise :: following) env, stack, heap⟩) :
    StepWithin (step module anchors ⟨.block (.forIn target (.dictionaryValuesIterable receiver) body otherwise :: following) env, stack, heap⟩ globals) := by
  have loopInside := inside.1.2 _ (List.mem_cons_self ..)
  simp only [StmtWithin] at loopInside
  refine ⟨inside.1.1, ?_⟩
  intro frame member
  rcases List.mem_cons.mp member with rfl | member
  · simp only [FrameWithin]
    exact ⟨inside.1.1, loopInside.1, loopInside.2, fun statement member => inside.1.2 statement (by simp [member])⟩
  · exact inside.2 frame member

theorem dictionary_start_within (heap : Mutable.Heap) (closed : Closed heap) (anchors : Nat)
    (valuesOnly : Bool) (target : Expr) (receiver : Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (receiverInside : receiver.edge.Within heap.length) (globalsInside : GlobalsWithin heap.length globals)
    (envInside : EnvWithin heap.length env) (stackInside : ∀ frame ∈ stack, FrameWithin heap.length frame)
    (bodyInside : ∀ statement ∈ body, StmtWithin heap.length statement)
    (otherwiseInside : ∀ statement ∈ otherwise, StmtWithin heap.length statement)
    (followingInside : ∀ statement ∈ following, StmtWithin heap.length statement) :
    StepWithin (if valuesOnly then dictionaryValuesStart anchors target body otherwise following env receiver stack heap globals
      else dictionaryItemsStart anchors target body otherwise following env receiver stack heap globals) := by
  have errorInside : StepWithin (done anchors heap (.error {typeName := "AttributeError", args := []}) globals) :=
    ⟨globalsInside, by intro value impossible; cases impossible⟩
  have customInside (method : String) : StepWithin (match target with
      | .name name => Step.next ⟨.value receiver,
          .methodReceiver method [] env :: .sequence name body otherwise following env :: stack, heap⟩
      | .tuple targets | .list targets => match Calls.targetNames targets with
          | some names => .next ⟨.value receiver,
              .methodReceiver method [] env :: .unpackSequence names body otherwise following env :: stack, heap⟩
          | none => .unsupported
      | _ => .unsupported) := by
    have saved (frame : Frame) (frameInside : FrameWithin heap.length frame) :
        StepWithin (.next ⟨.value receiver, .methodReceiver method [] env :: frame :: stack, heap⟩) := by
      refine ⟨receiverInside, ?_⟩
      intro current member
      rcases List.mem_cons.mp member with rfl | member
      · simpa only [FrameWithin] using envInside
      rcases List.mem_cons.mp member with rfl | member
      · exact frameInside
      · exact stackInside current member
    split <;> try (first
      | exact saved _ (by simpa only [FrameWithin] using And.intro envInside (And.intro bodyInside (And.intro otherwiseInside followingInside)))
      | trivial)
    all_goals split <;> first
      | exact saved _ (by simpa only [FrameWithin] using And.intro envInside (And.intro bodyInside (And.intro otherwiseInside followingInside)))
      | trivial
  cases receiver with
  | scalar value => cases valuesOnly <;> exact errorInside
  | ref address =>
    have found : heap[address]? = some heap[address] := List.getElem?_eq_getElem receiverInside
    cases fields : dictionaryItemFields heap[address] with
    | none =>
      cases valuesOnly <;> simp only [Bool.false_eq_true, if_false, if_true, dictionaryItemsStart, dictionaryValuesStart, found, fields]
      all_goals
        cases object : heap[address] <;> simp only [dictionaryItemFields] at fields
        all_goals first | contradiction | exact errorInside | exact customInside "items" | exact customInside "values"
    | some entries =>
      have entriesInside := dictionaryItemFields_within heap.length heap[address] entries
        (closed heap[address] (List.mem_of_getElem? found)) fields
      have keysInside : ∀ key ∈ entries.map (fun entry => sequenceSource entry.1), SourceWithin heap.length key := by
        intro key member
        obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
        exact sequenceSource_within heap.length entry.1 (entriesInside entry present).1
      have cursorInside (name : String) (loopBody : List Stmt)
          (bounded : ∀ statement ∈ loopBody, StmtWithin heap.length statement) :
          StepWithin (.next ⟨.block (.dictionaryItemsStepLoop name address
            (entries.map fun entry => sequenceSource entry.1) 0 loopBody otherwise :: following) env, stack, heap⟩) := by
        refine ⟨⟨envInside, ?_⟩, stackInside⟩
        intro statement member
        rcases List.mem_cons.mp member with rfl | member
        · simp only [StmtWithin]
          exact ⟨receiverInside, keysInside, bounded, otherwiseInside⟩
        · exact followingInside statement member
      cases valuesOnly with
      | false =>
        simp only [Bool.false_eq_true, if_false, dictionaryItemsStart, found, fields]
        exact cursorInside _ _ (comprehensionTargetBody_within heap.length target body bodyInside)
      | true =>
        simp only [if_true, dictionaryValuesStart, found, fields]
        exact cursorInside _ _ (dictionaryValuesBody_within heap.length target body bodyInside)

theorem StateWithin.dictionary_items_start (heap : Mutable.Heap) (closed : Closed heap) (anchors : Nat)
    (target : Expr) (receiver : Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (globalsInside : GlobalsWithin heap.length globals)
    (inside : StateWithin ⟨.value receiver, .dictionaryItemsReceiver target body otherwise following env :: stack, heap⟩) :
    StepWithin (step module anchors ⟨.value receiver, .dictionaryItemsReceiver target body otherwise following env :: stack, heap⟩ globals) := by
  have saved := inside.2 _ (List.mem_cons_self ..)
  simp only [FrameWithin] at saved
  simp only [step]
  apply protectGenerator_within
  exact dictionary_start_within heap closed anchors false target receiver body otherwise following env stack globals
    inside.1 globalsInside saved.1 (fun frame member => inside.2 frame (by simp [member]))
    saved.2.1 saved.2.2.1 saved.2.2.2

theorem StateWithin.dictionary_values_start (heap : Mutable.Heap) (closed : Closed heap) (anchors : Nat)
    (target : Expr) (receiver : Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (globalsInside : GlobalsWithin heap.length globals)
    (inside : StateWithin ⟨.value receiver, .dictionaryValuesReceiver target body otherwise following env :: stack, heap⟩) :
    StepWithin (step module anchors ⟨.value receiver, .dictionaryValuesReceiver target body otherwise following env :: stack, heap⟩ globals) := by
  have saved := inside.2 _ (List.mem_cons_self ..)
  simp only [FrameWithin] at saved
  simp only [step]
  apply protectGenerator_within
  exact dictionary_start_within heap closed anchors true target receiver body otherwise following env stack globals
    inside.1 globalsInside saved.1 (fun frame member => inside.2 frame (by simp [member]))
    saved.2.1 saved.2.2.1 saved.2.2.2

end FormalSW.PyAst.HeapCalls.Relocation
