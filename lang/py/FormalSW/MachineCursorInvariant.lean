import lang.py.FormalSW.MachineStatementInvariant
import lang.py.FormalSW.MachineExceptionInvariant

/-! Allocating loop cursors retain both heaps and the roots needed by the next step. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

variable (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
  (logicalAnchors physicalAnchors : Nat)

theorem step_positional_loop_preserves (layout : ExecutionLayout logical physical rename)
    (name : String) (rows : List (List SequenceSource)) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin ⟨.block (.permutationStepLoop name rows body otherwise :: following) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.permutationStepLoop name rows body otherwise :: following) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.block (.permutationStepLoop name rows body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have loopInside := inside.1.2 _ (List.mem_cons_self ..)
  have restInside : ∀ statement ∈ following, StmtWithin logical.length statement :=
    fun statement member => inside.1.2 statement (by simp [member])
  simp only [StmtWithin] at loopInside
  cases rows with
  | nil =>
    refine ⟨logical, physical, rename, (fun _ _ => rfl), Nat.le_refl _, Nat.le_refl _, layout, ?_, ?_, ?_⟩
    · simp [step, StepHeap]
    · simp only [step, protectGenerator_next]
      exact ⟨⟨inside.1.1, by
        simpa only [List.mem_append, or_imp, forall_and] using And.intro loopInside.2.2 restInside⟩, inside.2⟩
    · simp [relocateState, relocateWork, relocateStmt, step, relocateStep]
  | cons row rows =>
    have nextInside := loopContinuation_within logical.length body (.permutationStepLoop name rows body otherwise)
      (by
        simpa only [StmtWithin] using And.intro
          (fun row member => loopInside.1 row (List.mem_cons_of_mem _ member)) loopInside.2)
    have fieldsInside : ∀ value ∈ row.map sequenceValue, value.edge.Within logical.length := by
      intro value member
      obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
      exact (loopInside.1 row (List.mem_cons_self ..) source present).value
    obtain ⟨address, physicalAddress, after, other, nextMap, first, second, retained, bounded, same, agree⟩ :=
      layout.allocateTuple (row.map sequenceValue) fieldsInside
    have larger := allocateTuple_length logical after (row.map sequenceValue) (.ref address) first
    have statementsInside : ∀ statement ∈ body ++ [Calls.loopContinuation body
        (.permutationStepLoop name rows body otherwise)] ++ following,
        StmtWithin logical.length statement := by
      simpa only [List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq]
        using And.intro (And.intro loopInside.2.1 nextInside) restInside
    have envSame := relocateEnv_congr nextMap rename logical.length env agree inside.1.1
    have stackSame := relocateStack_congr nextMap rename logical.length stack agree inside.2
    have statementsSame := List.map_congr_left (fun statement member =>
      relocateStmt_congr nextMap rename logical.length statement agree (statementsInside statement member))
    refine ⟨after, other, nextMap, agree, larger, allocateTuple_length physical other _ _ second,
      retained, ?_, ?_, ?_⟩
    · simp [step, run, first, StepHeap]
    · simp only [step, run, first, protectGenerator_next]
      exact ⟨⟨(inside.1.1.mono larger).setLocal name (.ref address) bounded,
        fun statement member => (statementsInside statement member).mono larger⟩,
        fun frame member => (inside.2 frame member).mono larger⟩
    · simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step, row_values_relocate,
        run, first, second, protectGenerator_next, relocateStep]
      simp only [relocateEnv_set, relocateValue, same, envSame, stackSame]
      rw [statementsSame]
      simp only [List.map_append, List.map_cons, List.map_nil, ← loopContinuation_relocate, relocateStmt]

theorem step_zip_loop_preserves (layout : ExecutionLayout logical physical rename)
    (name : String) (sources : List SequenceSource) (position : Nat) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (globalsInside : GlobalsWithin logical.length globals)
    (inside : StateWithin ⟨.block (.zipStepLoop name sources position body otherwise :: following) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.zipStepLoop name sources position body otherwise :: following) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.block (.zipStepLoop name sources position body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have loopInside := inside.1.2 _ (List.mem_cons_self ..)
  have restInside : ∀ statement ∈ following, StmtWithin logical.length statement :=
    fun statement member => inside.1.2 statement (by simp [member])
  have nextInside := loopContinuation_within logical.length body
    (.zipStepLoop name sources (position + 1) body otherwise) (by simpa only [StmtWithin] using loopInside)
  simp only [StmtWithin] at loopInside
  have paired := zipItem_relocates layout.runtime sources position loopInside.1
  cases fetched : zipItem sources position logical with
  | none =>
    refine ⟨logical, physical, rename, (fun _ _ => rfl), Nat.le_refl _, Nat.le_refl _, layout, ?_, ?_, ?_⟩
    · simp [step, run, fetched, StepHeap, protectGenerator]
    · simp [step, run, fetched, StepWithin, protectGenerator]
    · simp [relocateState, relocateWork, relocateStmt, step, run, paired, fetched, relocateStep]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have unchanged := zipItem_keeps_heap logical sources position outcome after fetched
    subst after
    cases outcome with
    | error exception =>
      refine ⟨logical, physical, rename, (fun _ _ => rfl), Nat.le_refl _, Nat.le_refl _, layout, ?_, ?_, ?_⟩
      · simp [step, run, fetched, StepHeap, protectGenerator, done]
      · apply protectGenerator_within
        simp only [run, fetched, done]
        exact ⟨globalsInside, by intro value impossible; cases impossible⟩
      · simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step]
        rw [← protectGenerator_relocates]
        congr 1
        simp [run, paired, fetched, done, relocateStep, relocateCompletion, Except.map]
    | ok fields =>
      cases fields with
      | none =>
        refine ⟨logical, physical, rename, (fun _ _ => rfl), Nat.le_refl _, Nat.le_refl _, layout, ?_, ?_, ?_⟩
        · simp [step, run, fetched, StepHeap, protectGenerator]
        · simp only [step, run, fetched, protectGenerator_next]
          exact ⟨⟨inside.1.1, by
            simpa only [List.mem_append, or_imp, forall_and]
              using And.intro loopInside.2.2 restInside⟩, inside.2⟩
        · simp [relocateState, relocateWork, relocateStmt, step, run, paired, fetched, relocateStep, Except.map]
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
        refine ⟨after, other, nextMap, agree, larger, allocateTuple_length physical other _ _ second,
          retained, ?_, ?_, ?_⟩
        · simp [step, run, fetched, first, StepHeap]
        · simp only [step, run, fetched, first, protectGenerator_next]
          exact ⟨⟨(inside.1.1.mono larger).setLocal name (.ref address) bounded,
            fun statement member => (statementsInside statement member).mono larger⟩,
            fun frame member => (inside.2 frame member).mono larger⟩
        · simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step, run, paired, fetched,
            Option.map_some, Except.map, first, second, protectGenerator_next, relocateStep]
          simp only [relocateEnv_set, relocateValue, same, envSame, stackSame]
          rw [statementsSame]
          simp only [List.map_append, List.map_cons, List.map_nil, ← loopContinuation_relocate, relocateStmt]

theorem step_dictionary_items_loop_preserves (layout : ExecutionLayout logical physical rename)
    (name : String) (address : Nat) (keys : List SequenceSource) (position : Nat) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (globalsInside : GlobalsWithin logical.length globals)
    (inside : StateWithin ⟨.block (.dictionaryItemsStepLoop name address keys position body otherwise :: following) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.dictionaryItemsStepLoop name address keys position body otherwise :: following) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.block (.dictionaryItemsStepLoop name address keys position body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have loopInside := inside.1.2 _ (List.mem_cons_self ..)
  have restInside : ∀ statement ∈ following, StmtWithin logical.length statement :=
    fun statement member => inside.1.2 statement (by simp [member])
  have nextInside := loopContinuation_within logical.length body
    (.dictionaryItemsStepLoop name address keys (position + 1) body otherwise) (by simpa only [StmtWithin] using loopInside)
  simp only [StmtWithin] at loopInside
  have paired := dictionaryItemsNext_relocates layout.runtime layout.closed address keys position loopInside.1 loopInside.2.1
  cases fetched : dictionaryItemsNext address keys position logical with
  | none =>
    refine ⟨logical, physical, rename, (fun _ _ => rfl), Nat.le_refl _, Nat.le_refl _, layout, ?_, ?_, ?_⟩
    · simp [step, run, fetched, StepHeap, protectGenerator]
    · simp [step, run, fetched, StepWithin, protectGenerator]
    · simp [relocateState, relocateWork, relocateStmt, step, run, paired, fetched, relocateStep]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have unchanged := dictionaryItemsNext_keeps_heap logical address keys position outcome after fetched
    subst after
    cases outcome with
    | error exception =>
      refine ⟨logical, physical, rename, (fun _ _ => rfl), Nat.le_refl _, Nat.le_refl _, layout, ?_, ?_, ?_⟩
      · simp [step, run, fetched, StepHeap, protectGenerator, done]
      · apply protectGenerator_within
        simp only [run, fetched, done]
        exact ⟨globalsInside, by intro value impossible; cases impossible⟩
      · simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step]
        rw [← protectGenerator_relocates]
        congr 1
        simp [run, paired, fetched, done, relocateStep, relocateCompletion, Except.map]
    | ok fields =>
      cases fields with
      | none =>
        refine ⟨logical, physical, rename, (fun _ _ => rfl), Nat.le_refl _, Nat.le_refl _, layout, ?_, ?_, ?_⟩
        · simp [step, run, fetched, StepHeap, protectGenerator]
        · simp only [step, run, fetched, protectGenerator_next]
          exact ⟨⟨inside.1.1, by
            simpa only [List.mem_append, or_imp, forall_and]
              using And.intro loopInside.2.2.2 restInside⟩, inside.2⟩
        · simp [relocateState, relocateWork, relocateStmt, step, run, paired, fetched, relocateStep, Except.map]
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
        refine ⟨after, other, nextMap, agree, larger, allocateTuple_length physical other _ _ second,
          retained, ?_, ?_, ?_⟩
        · simp [step, run, fetched, first, StepHeap]
        · simp only [step, run, fetched, first, protectGenerator_next]
          exact ⟨⟨(inside.1.1.mono larger).setLocal name (.ref tupleAddress) bounded,
            fun statement member => (statementsInside statement member).mono larger⟩,
            fun frame member => (inside.2 frame member).mono larger⟩
        · simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step, run, paired, fetched,
            Option.map_some, Except.map, relocatePair, first, second, protectGenerator_next, relocateStep]
          simp only [relocateEnv_set, relocateValue, same, envSame, stackSame]
          rw [statementsSame]
          simp only [List.map_append, List.map_cons, List.map_nil, ← loopContinuation_relocate, relocateStmt]

end FormalSW.PyAst.HeapCalls.Relocation
