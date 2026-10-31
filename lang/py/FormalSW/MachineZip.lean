import lang.py.FormalSW.MachineReverse
import lang.py.FormalSW.ZipCalls

/-! Zip captures its sources once and reads current fields from left to right. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem readonly_bind_relocates {α β γ δ : Type} (logical physical : Mutable.Heap)
    (read : Mutable.Eval α) (otherRead : Mutable.Eval β) (mapInput : α → β) (mapOutput : γ → δ)
    (next : α → Mutable.Eval γ) (otherNext : β → Mutable.Eval δ)
    (readonly : ∀ outcome after, read logical = some (outcome, after) → after = logical)
    (paired : otherRead physical = (read logical).map (fun pair => (pair.1.map mapInput, physical)))
    (following : ∀ value, read logical = some (.ok value, logical) →
      otherNext (mapInput value) physical = (next value logical).map (fun pair => (pair.1.map mapOutput, physical))) :
    (otherRead >>= otherNext) physical =
      ((read >>= next) logical).map (fun pair => (pair.1.map mapOutput, physical)) := by
  cases tested : read logical with
  | none => simp [Mutable.eval_bind, paired, tested]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have same := readonly outcome after tested
    subst after
    cases outcome with
    | error exception => simp [Mutable.eval_bind, paired, tested, Except.map]
    | ok value => simpa [Mutable.eval_bind, paired, tested] using following value tested

theorem readonly_bind_keeps_heap {α β : Type} (heap : Mutable.Heap)
    (read : Mutable.Eval α) (next : α → Mutable.Eval β)
    (readonly : ∀ outcome after, read heap = some (outcome, after) → after = heap)
    (following : ∀ value, read heap = some (.ok value, heap) →
      ∀ outcome after, next value heap = some (outcome, after) → after = heap)
    (outcome : Except ExceptionObject β) (after : Mutable.Heap)
    (executed : (read >>= next) heap = some (outcome, after)) : after = heap := by
  cases tested : read heap with
  | none => simp [Mutable.eval_bind, tested] at executed
  | some pair =>
    rcases pair with ⟨result, middle⟩
    have same := readonly result middle tested
    subst middle
    cases result with
    | error exception => simpa [Mutable.eval_bind, tested] using (congrArg (Option.map Prod.snd) executed).symm
    | ok value => exact following value tested outcome after (by simpa [Mutable.eval_bind, tested] using executed)

theorem zipSources_cons (value : Value) (values : List Value) :
    zipSources (value :: values) = (do
      let _ ← Mutable.sequence value
      let rest ← zipSources values
      pure (sequenceSource value :: rest)) := by
  simp [zipSources, List.mapM_cons]

theorem zipSources_keeps_heap (heap : Mutable.Heap) (values : List Value)
    (outcome : Except ExceptionObject (List SequenceSource)) (after : Mutable.Heap)
    (executed : zipSources values heap = some (outcome, after)) : after = heap := by
  induction values generalizing outcome after with
  | nil => simpa [zipSources] using (congrArg (Option.map Prod.snd) executed).symm
  | cons value values ih =>
    rw [zipSources_cons] at executed
    apply readonly_bind_keeps_heap heap _ _
      (fun result middle read => sequence_keeps_heap heap middle value result read) _ outcome after executed
    intro items read result middle continued
    apply readonly_bind_keeps_heap heap _ _ (fun result middle read => ih result middle read) _ result middle continued
    intro sources captured result final returned
    simpa using (congrArg (Option.map Prod.snd) returned).symm

theorem zipFields_keeps_heap (heap : Mutable.Heap) (sources : List SequenceSource) (position : Nat)
    (outcome : Except ExceptionObject (Option (List Value))) (after : Mutable.Heap)
    (executed : zipFields sources position heap = some (outcome, after)) : after = heap := by
  induction sources generalizing outcome after with
  | nil => simpa [zipFields] using (congrArg (Option.map Prod.snd) executed).symm
  | cons source sources ih =>
    apply readonly_bind_keeps_heap heap _ _
      (fun result middle read => sequence_keeps_heap heap middle (sequenceValue source) result read) _ outcome after executed
    intro items read result middle continued
    cases found : items[position]? with
    | none => simpa [found] using (congrArg (Option.map Prod.snd) continued).symm
    | some value =>
      simp only [found] at continued
      apply readonly_bind_keeps_heap heap _ _ (fun result middle read => ih result middle read) _ result middle continued
      intro fields fetched result final returned
      simpa using (congrArg (Option.map Prod.snd) returned).symm

theorem zipItem_keeps_heap (heap : Mutable.Heap) (sources : List SequenceSource) (position : Nat)
    (outcome : Except ExceptionObject (Option (List Value))) (after : Mutable.Heap)
    (executed : zipItem sources position heap = some (outcome, after)) : after = heap := by
  cases sources with
  | nil => simpa [zipItem] using (congrArg (Option.map Prod.snd) executed).symm
  | cons source sources => exact zipFields_keeps_heap heap (source :: sources) position outcome after executed

theorem zipSources_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (values : List Value)
    (inside : ∀ value ∈ values, value.edge.Within logical.length) :
    zipSources (values.map (relocateValue rename)) physical =
      (zipSources values logical).map (fun pair => (pair.1.map (List.map (relocateSource rename)), physical)) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [List.map_cons, zipSources_cons]
    apply readonly_bind_relocates logical physical _ _ (List.map (relocateValue rename)) _ _ _
      (fun result after read => sequence_keeps_heap logical after value result read)
      (layout.sequence value (inside value (by simp)))
    intro items read
    apply readonly_bind_relocates logical physical _ _ (List.map (relocateSource rename)) _ _ _
      (fun result after captured => zipSources_keeps_heap logical values result after captured)
      (ih (fun item member => inside item (by simp [member])))
    intro sources captured
    simp [sequenceSource_relocate, Except.map]

theorem zipFields_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (sources : List SequenceSource) (position : Nat)
    (inside : ∀ source ∈ sources, SourceWithin logical.length source) :
    zipFields (sources.map (relocateSource rename)) position physical =
      (zipFields sources position logical).map
        (fun pair => (pair.1.map (Option.map (List.map (relocateValue rename))), physical)) := by
  induction sources with
  | nil => rfl
  | cons source sources ih =>
    simp only [List.map_cons, zipFields, sequenceValue_relocate]
    apply readonly_bind_relocates logical physical _ _ (List.map (relocateValue rename)) _ _ _
      (fun result after read => sequence_keeps_heap logical after (sequenceValue source) result read)
      (layout.sequence (sequenceValue source) (inside source (by simp)).value)
    intro items read
    simp only [List.getElem?_map]
    cases found : items[position]? with
    | none => rfl
    | some value =>
      simp only [Option.map_some]
      apply readonly_bind_relocates logical physical _ _ (Option.map (List.map (relocateValue rename))) _ _ _
        (fun result after fetched => zipFields_keeps_heap logical sources position result after fetched)
        (ih (fun item member => inside item (by simp [member])))
      intro fields fetched
      cases fields <;> rfl

theorem zipItem_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (sources : List SequenceSource) (position : Nat)
    (inside : ∀ source ∈ sources, SourceWithin logical.length source) :
    zipItem (sources.map (relocateSource rename)) position physical =
      (zipItem sources position logical).map
        (fun pair => (pair.1.map (Option.map (List.map (relocateValue rename))), physical)) := by
  cases sources with
  | nil => rfl
  | cons source sources => exact zipFields_relocates layout (source :: sources) position inside

theorem readonly_bind_success {α β : Type} (heap : Mutable.Heap)
    (read : Mutable.Eval α) (next : α → Mutable.Eval β)
    (readonly : ∀ outcome after, read heap = some (outcome, after) → after = heap)
    (value : β) (after : Mutable.Heap) (executed : (read >>= next) heap = some (.ok value, after)) :
    ∃ input, read heap = some (.ok input, heap) ∧ next input heap = some (.ok value, after) := by
  cases tested : read heap with
  | none => simp [Mutable.eval_bind, tested] at executed
  | some pair =>
    rcases pair with ⟨result, middle⟩
    have same := readonly result middle tested
    subst middle
    cases result with
    | error exception => simp [Mutable.eval_bind, tested] at executed
    | ok input => exact ⟨input, rfl, by simpa [Mutable.eval_bind, tested] using executed⟩

theorem zipSources_captured (heap : Mutable.Heap) (values : List Value) (sources : List SequenceSource)
    (executed : zipSources values heap = some (.ok sources, heap)) : sources = values.map sequenceSource := by
  induction values generalizing sources with
  | nil => simpa [zipSources] using executed.symm
  | cons value values ih =>
    rw [zipSources_cons] at executed
    obtain ⟨items, _, continued⟩ := readonly_bind_success heap _ _
      (fun result after read => sequence_keeps_heap heap after value result read) sources heap executed
    obtain ⟨rest, captured, returned⟩ := readonly_bind_success heap _ _
      (fun result after read => zipSources_keeps_heap heap values result after read) sources heap continued
    have same : sources = sequenceSource value :: rest := by simpa using returned.symm
    simpa [ih rest captured] using same

theorem zipFields_values_within (heap : Mutable.Heap) (closed : Closed heap)
    (sources : List SequenceSource) (position : Nat) (fields : List Value)
    (executed : zipFields sources position heap = some (.ok (some fields), heap)) :
    ∀ value ∈ fields, value.edge.Within heap.length := by
  induction sources generalizing fields with
  | nil =>
    have empty : fields = [] := by simpa [zipFields] using executed.symm
    simp [empty]
  | cons source sources ih =>
    obtain ⟨items, read, continued⟩ := readonly_bind_success heap _ _
      (fun result after read => sequence_keeps_heap heap after (sequenceValue source) result read) (some fields) heap executed
    cases found : items[position]? with
    | none => simp [found] at continued
    | some value =>
      simp only [found] at continued
      obtain ⟨rest, fetched, returned⟩ := readonly_bind_success heap _ _
        (fun result after read => zipFields_keeps_heap heap sources position result after read) (some fields) heap continued
      cases rest with
      | none => simp at returned
      | some rest =>
        have same : fields = value :: rest := by simpa using returned.symm
        subst fields
        intro item member
        rcases List.mem_cons.mp member with rfl | member
        · exact sequence_items_within heap heap closed (sequenceValue source) items read item (List.mem_of_getElem? found)
        · exact ih rest fetched item member

theorem zipItem_values_within (heap : Mutable.Heap) (closed : Closed heap)
    (sources : List SequenceSource) (position : Nat) (fields : List Value)
    (executed : zipItem sources position heap = some (.ok (some fields), heap)) :
    ∀ value ∈ fields, value.edge.Within heap.length := by
  cases sources with
  | nil => simp [zipItem] at executed
  | cons source sources => exact zipFields_values_within heap closed (source :: sources) position fields executed

theorem comprehensionTargetBody_relocates (rename : Nat → Nat) (target : Expr) (body : List Stmt) :
    comprehensionTargetBody target (body.map (relocateStmt rename)) =
      (comprehensionTargetBody target body).map (relocateStmt rename) := by
  cases target <;> simp [comprehensionTargetBody, relocateStmt]

theorem comprehensionTargetBody_within (limit : Nat) (target : Expr) (body : List Stmt)
    (inside : ∀ statement ∈ body, StmtWithin limit statement) :
    ∀ statement ∈ comprehensionTargetBody target body, StmtWithin limit statement := by
  cases target <;> simp_all [comprehensionTargetBody, StmtWithin]

variable (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
  (logicalAnchors physicalAnchors : Nat)

theorem step_for_zip_relocates (target : Expr) (expressions : List Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.block (.forZip target expressions body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.block (.forZip target expressions body otherwise :: following) env, stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step, protectGenerator_next, relocateStep]
  exact congrArg Step.next (argumentsState_relocates rename logical physical
    (.zipStart target body otherwise following env) env [] expressions stack)

theorem step_zip_start_relocates (layout : RuntimeLayout logical physical rename)
    (target : Expr) (values : List Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : ∀ value ∈ values, value.edge.Within logical.length) :
    step module physicalAnchors
        (relocateState rename physical ⟨.operation (.zipStart target body otherwise following env) values, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.operation (.zipStart target body otherwise following env) values, stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, relocateRuntimeOperation, step]
  rw [← protectGenerator_relocates]
  congr 1
  apply run_readonly_relocates logical physical rename logicalAnchors physicalAnchors _ _
    (List.map (relocateSource rename)) globals
    (fun outcome after executed => zipSources_keeps_heap logical values outcome after executed)
    (zipSources_relocates layout values inside)
  intro sources captured
  simp only [relocateStep, relocateState, relocateWork, List.map_cons, relocateStmt, comprehensionTargetBody_relocates]

theorem StateWithin.for_zip (heap : Mutable.Heap) (anchors : Nat)
    (target : Expr) (expressions : List Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin ⟨.block (.forZip target expressions body otherwise :: following) env, stack, heap⟩) :
    StepWithin (step module anchors ⟨.block (.forZip target expressions body otherwise :: following) env, stack, heap⟩ globals) := by
  have loopInside := inside.1.2 _ (List.mem_cons_self ..)
  simp only [StmtWithin] at loopInside
  apply argumentsState_within heap _ env [] expressions stack _ inside.1.1 (by simp) inside.2
  exact ⟨inside.1.1, loopInside.1, loopInside.2, fun statement member => inside.1.2 statement (by simp [member])⟩

theorem StateWithin.zip_start (heap : Mutable.Heap) (anchors : Nat)
    (target : Expr) (values : List Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (globalsInside : GlobalsWithin heap.length globals)
    (inside : StateWithin ⟨.operation (.zipStart target body otherwise following env) values, stack, heap⟩) :
    StepWithin (step module anchors ⟨.operation (.zipStart target body otherwise following env) values, stack, heap⟩ globals) := by
  have saved := inside.1.1
  simp only [OperationWithin] at saved
  simp only [step]
  apply protectGenerator_within
  apply run_readonly_within heap anchors (zipSources values) globals globalsInside
    (fun outcome after executed => zipSources_keeps_heap heap values outcome after executed)
  intro sources captured
  refine ⟨⟨saved.1, ?_⟩, inside.2⟩
  intro statement member
  rcases List.mem_cons.mp member with rfl | member
  · simp only [StmtWithin]
    refine ⟨?_, comprehensionTargetBody_within heap.length target body saved.2.1, saved.2.2.1⟩
    rw [zipSources_captured heap values sources captured]
    intro source member
    obtain ⟨value, valueMember, rfl⟩ := List.mem_map.mp member
    exact sequenceSource_within heap.length value (inside.1.2 value valueMember)
  · exact saved.2.2.2 statement member

/-- Each successful row allocates a tuple; stopped reads retain the old layout. -/
theorem step_zip_loop_relocates (layout : ExecutionLayout logical physical rename)
    (name : String) (sources : List SequenceSource) (position : Nat) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (globalsInside : GlobalsWithin logical.length globals)
    (inside : StateWithin ⟨.block (.zipStepLoop name sources position body otherwise :: following) env, stack, logical⟩) :
    ∃ after other nextMap, ExecutionLayout after other nextMap ∧
      logical.length ≤ after.length ∧ (∀ address < logical.length, nextMap address = rename address) ∧
      GlobalsWithin after.length globals ∧ relocateGlobals nextMap globals = relocateGlobals rename globals ∧
      step module physicalAnchors
          (relocateState rename physical ⟨.block (.zipStepLoop name sources position body otherwise :: following) env, stack, logical⟩)
          (relocateGlobals rename globals) =
        relocateStep nextMap other physicalAnchors
          (step module logicalAnchors ⟨.block (.zipStepLoop name sources position body otherwise :: following) env, stack, logical⟩ globals) ∧
      StepWithin (step module logicalAnchors ⟨.block (.zipStepLoop name sources position body otherwise :: following) env, stack, logical⟩ globals) := by
  have loopInside := inside.1.2 _ (List.mem_cons_self ..)
  have restInside : ∀ statement ∈ following, StmtWithin logical.length statement :=
    fun statement member => inside.1.2 statement (by simp [member])
  have nextInside := loopContinuation_within logical.length body
    (.zipStepLoop name sources (position + 1) body otherwise) (by simpa only [StmtWithin] using loopInside)
  simp only [StmtWithin] at loopInside
  have paired := zipItem_relocates layout.runtime sources position loopInside.1
  cases fetched : zipItem sources position logical with
  | none =>
    refine ⟨logical, physical, rename, layout, Nat.le_refl _, fun _ _ => rfl, globalsInside, rfl, ?_, ?_⟩
    · simp [relocateState, relocateWork, relocateStmt, step, run, paired, fetched, relocateStep]
    · simp [step, run, fetched, StepWithin, protectGenerator]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have unchanged := zipItem_keeps_heap logical sources position outcome after fetched
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
              using And.intro loopInside.2.2 restInside⟩, inside.2⟩
      | some fields =>
        have fieldsInside := zipItem_values_within logical layout.closed sources position fields fetched
        obtain ⟨address, physicalAddress, after, other, nextMap, first, second, retained, bounded, same, agree⟩ :=
          layout.allocateTuple fields fieldsInside
        have larger := allocateTuple_length logical after fields (.ref address) first
        have statementsInside : ∀ statement ∈ body ++ [Calls.loopContinuation body
            (.zipStepLoop name sources (position + 1) body otherwise)] ++ following,
            StmtWithin logical.length statement := by
          simpa only [List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq]
            using And.intro (And.intro loopInside.2.1 nextInside) restInside
        have envSame := relocateEnv_congr nextMap rename logical.length env agree inside.1.1
        have stackSame := relocateStack_congr nextMap rename logical.length stack agree inside.2
        have statementsSame := List.map_congr_left (fun statement member =>
          relocateStmt_congr nextMap rename logical.length statement agree (statementsInside statement member))
        refine ⟨after, other, nextMap, retained, larger, agree, globalsInside.mono larger,
          relocateGlobals_congr nextMap rename logical.length globals agree globalsInside, ?_, ?_⟩
        · simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step, run, paired, fetched,
            Option.map_some, Except.map, first, second, protectGenerator_next, relocateStep]
          simp only [relocateEnv_set, relocateValue, same, envSame, stackSame]
          rw [statementsSame]
          simp only [List.map_append, List.map_cons, List.map_nil, ← loopContinuation_relocate, relocateStmt]
        · simp only [step, run, fetched, first, protectGenerator_next]
          exact ⟨⟨(inside.1.1.mono larger).setLocal name (.ref address) bounded,
            fun statement member => (statementsInside statement member).mono larger⟩,
            fun frame member => (inside.2 frame member).mono larger⟩

end FormalSW.PyAst.HeapCalls.Relocation
