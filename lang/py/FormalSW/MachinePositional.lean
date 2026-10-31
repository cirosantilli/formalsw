import lang.py.FormalSW.PositionalRelocation
import lang.py.FormalSW.PermutationCalls
import lang.py.FormalSW.CombinationCalls

/-! Positional loop steps preserve captured rows and extending tuple allocations. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

/-- Tuple interning either retains the heap or appends one object. -/
theorem allocateTuple_preserves_lookup (heap after : Mutable.Heap) (items : List Value) (value : Value)
    (address : Nat) (object : Mutable.Object) (found : heap[address]? = some object)
    (executed : Mutable.allocateTuple items heap = some (.ok value, after)) : after[address]? = some object := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have extension : after = heap ∨ after = heap ++ [.tuple items] := by
    cases items with
    | nil =>
      cases selected : heap.findIdx? (fun object => decide (object = .tuple [])) with
      | none => exact Or.inr (by simpa [Mutable.allocateTuple, selected] using (congrArg (Option.map Prod.snd) executed).symm)
      | some index => exact Or.inl (by simpa [Mutable.allocateTuple, selected] using (congrArg (Option.map Prod.snd) executed).symm)
    | cons head tail => exact Or.inr (by simpa [Mutable.allocateTuple] using (congrArg (Option.map Prod.snd) executed).symm)
  rcases extension with rfl | rfl
  · exact found
  · rw [List.getElem?_append_left bound, found]

variable (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
  (logicalAnchors physicalAnchors : Nat)

theorem step_for_permutations_relocates (target : Expr) (expressions : List Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.block (.forIn target (.permutationsIterable expressions) body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.block (.forIn target (.permutationsIterable expressions) body otherwise :: following) env, stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step, protectGenerator_next, relocateStep]
  exact congrArg Step.next (argumentsState_relocates rename logical physical
    (.permutationStart target body otherwise following env) env [] expressions stack)

theorem step_permutation_start_relocates (layout : RuntimeLayout logical physical rename)
    (target : Expr) (values : List Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : ∀ value ∈ values, value.edge.Within logical.length) :
    step module physicalAnchors
        (relocateState rename physical ⟨.operation (.permutationStart target body otherwise following env) values, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.operation (.permutationStart target body otherwise following env) values, stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, relocateRuntimeOperation, step]
  rw [← protectGenerator_relocates]
  congr 1
  apply run_readonly_relocates logical physical rename logicalAnchors physicalAnchors _ _
    (List.map (List.map (relocateSource rename))) globals
    (fun outcome after executed => permutationRows_keeps_heap logical values outcome after executed)
    (permutationRows_relocates layout values inside)
  intro rows captured
  simp only [relocateStep, relocateState, relocateWork, List.map_cons, relocateStmt, comprehensionTargetBody_relocates]

theorem StateWithin.for_permutations (heap : Mutable.Heap) (anchors : Nat)
    (target : Expr) (expressions : List Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin ⟨.block (.forIn target (.permutationsIterable expressions) body otherwise :: following) env, stack, heap⟩) :
    StepWithin (step module anchors ⟨.block (.forIn target (.permutationsIterable expressions) body otherwise :: following) env, stack, heap⟩ globals) := by
  have loopInside := inside.1.2 _ (List.mem_cons_self ..)
  simp only [StmtWithin] at loopInside
  apply argumentsState_within heap _ env [] expressions stack _ inside.1.1 (by simp) inside.2
  exact ⟨inside.1.1, loopInside.1, loopInside.2, fun statement member => inside.1.2 statement (by simp [member])⟩

theorem StateWithin.permutation_start (heap : Mutable.Heap) (closed : Closed heap) (anchors : Nat)
    (target : Expr) (values : List Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (globalsInside : GlobalsWithin heap.length globals)
    (inside : StateWithin ⟨.operation (.permutationStart target body otherwise following env) values, stack, heap⟩) :
    StepWithin (step module anchors ⟨.operation (.permutationStart target body otherwise following env) values, stack, heap⟩ globals) := by
  have saved := inside.1.1
  simp only [OperationWithin] at saved
  simp only [step]
  apply protectGenerator_within
  apply run_readonly_within heap anchors (permutationRows values) globals globalsInside
    (fun outcome after executed => permutationRows_keeps_heap heap values outcome after executed)
  intro rows captured
  refine ⟨⟨saved.1, ?_⟩, inside.2⟩
  intro statement member
  rcases List.mem_cons.mp member with rfl | member
  · simp only [StmtWithin]
    exact ⟨permutationRows_within heap closed values rows captured,
      comprehensionTargetBody_within heap.length target body saved.2.1, saved.2.2.1⟩
  · exact saved.2.2.2 statement member

theorem step_for_combinations_relocates (target : Expr) (expressions : List Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.block (.forIn target (.combinationsIterable expressions) body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.block (.forIn target (.combinationsIterable expressions) body otherwise :: following) env, stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step, protectGenerator_next, relocateStep]
  exact congrArg Step.next (argumentsState_relocates rename logical physical
    (.combinationStart target body otherwise following env) env [] expressions stack)

theorem step_combination_start_relocates (layout : RuntimeLayout logical physical rename)
    (target : Expr) (values : List Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : ∀ value ∈ values, value.edge.Within logical.length) :
    step module physicalAnchors
        (relocateState rename physical ⟨.operation (.combinationStart target body otherwise following env) values, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.operation (.combinationStart target body otherwise following env) values, stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, relocateRuntimeOperation, step]
  rw [← protectGenerator_relocates]
  congr 1
  apply run_readonly_relocates logical physical rename logicalAnchors physicalAnchors _ _
    (List.map (List.map (relocateSource rename))) globals
    (fun outcome after executed => combinationRows_keeps_heap logical values outcome after executed)
    (combinationRows_relocates layout values inside)
  intro rows captured
  simp only [relocateStep, relocateState, relocateWork, List.map_cons, relocateStmt, comprehensionTargetBody_relocates]

theorem StateWithin.for_combinations (heap : Mutable.Heap) (anchors : Nat)
    (target : Expr) (expressions : List Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (inside : StateWithin ⟨.block (.forIn target (.combinationsIterable expressions) body otherwise :: following) env, stack, heap⟩) :
    StepWithin (step module anchors ⟨.block (.forIn target (.combinationsIterable expressions) body otherwise :: following) env, stack, heap⟩ globals) := by
  have loopInside := inside.1.2 _ (List.mem_cons_self ..)
  simp only [StmtWithin] at loopInside
  apply argumentsState_within heap _ env [] expressions stack _ inside.1.1 (by simp) inside.2
  exact ⟨inside.1.1, loopInside.1, loopInside.2, fun statement member => inside.1.2 statement (by simp [member])⟩

theorem StateWithin.combination_start (heap : Mutable.Heap) (closed : Closed heap) (anchors : Nat)
    (target : Expr) (values : List Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (globalsInside : GlobalsWithin heap.length globals)
    (inside : StateWithin ⟨.operation (.combinationStart target body otherwise following env) values, stack, heap⟩) :
    StepWithin (step module anchors ⟨.operation (.combinationStart target body otherwise following env) values, stack, heap⟩ globals) := by
  have saved := inside.1.1
  simp only [OperationWithin] at saved
  simp only [step]
  apply protectGenerator_within
  apply run_readonly_within heap anchors (combinationRows values) globals globalsInside
    (fun outcome after executed => combinationRows_keeps_heap heap values outcome after executed)
  intro rows captured
  refine ⟨⟨saved.1, ?_⟩, inside.2⟩
  intro statement member
  rcases List.mem_cons.mp member with rfl | member
  · simp only [StmtWithin]
    exact ⟨combinationRows_within heap closed values rows captured,
      comprehensionTargetBody_within heap.length target body saved.2.1, saved.2.2.1⟩
  · exact saved.2.2.2 statement member

theorem row_values_relocate (rename : Nat → Nat) (row : List SequenceSource) :
    (row.map (relocateSource rename)).map sequenceValue = (row.map sequenceValue).map (relocateValue rename) := by
  simp only [List.map_map, Function.comp_def, sequenceValue_relocate]

/-- Empty rows may reuse an interned empty tuple; other rows allocate fresh tuples. -/
theorem step_positional_loop_relocates (layout : ExecutionLayout logical physical rename)
    (name : String) (rows : List (List SequenceSource)) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (globalsInside : GlobalsWithin logical.length globals)
    (inside : StateWithin ⟨.block (.permutationStepLoop name rows body otherwise :: following) env, stack, logical⟩) :
    ∃ after other nextMap, ExecutionLayout after other nextMap ∧
      logical.length ≤ after.length ∧ (∀ address < logical.length, nextMap address = rename address) ∧
      GlobalsWithin after.length globals ∧ relocateGlobals nextMap globals = relocateGlobals rename globals ∧
      step module physicalAnchors
          (relocateState rename physical ⟨.block (.permutationStepLoop name rows body otherwise :: following) env, stack, logical⟩)
          (relocateGlobals rename globals) =
        relocateStep nextMap other physicalAnchors
          (step module logicalAnchors ⟨.block (.permutationStepLoop name rows body otherwise :: following) env, stack, logical⟩ globals) ∧
      StepWithin (step module logicalAnchors ⟨.block (.permutationStepLoop name rows body otherwise :: following) env, stack, logical⟩ globals) := by
  have loopInside := inside.1.2 _ (List.mem_cons_self ..)
  have restInside : ∀ statement ∈ following, StmtWithin logical.length statement :=
    fun statement member => inside.1.2 statement (by simp [member])
  simp only [StmtWithin] at loopInside
  cases rows with
  | nil =>
    refine ⟨logical, physical, rename, layout, Nat.le_refl _, fun _ _ => rfl, globalsInside, rfl, ?_, ?_⟩
    · simp [relocateState, relocateWork, relocateStmt, step, relocateStep]
    · simp only [step, protectGenerator_next]
      exact ⟨⟨inside.1.1, by
        simpa only [List.mem_append, or_imp, forall_and] using And.intro loopInside.2.2 restInside⟩, inside.2⟩
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
    refine ⟨after, other, nextMap, retained, larger, agree, globalsInside.mono larger,
      relocateGlobals_congr nextMap rename logical.length globals agree globalsInside, ?_, ?_⟩
    · simp only [relocateState, relocateWork, List.map_cons, relocateStmt, step, row_values_relocate,
        run, first, second, protectGenerator_next, relocateStep]
      simp only [relocateEnv_set, relocateValue, same, envSame, stackSame]
      rw [statementsSame]
      simp only [List.map_append, List.map_cons, List.map_nil, ← loopContinuation_relocate, relocateStmt]
    · simp only [step, run, first, protectGenerator_next]
      exact ⟨⟨(inside.1.1.mono larger).setLocal name (.ref address) bounded,
        fun statement member => (statementsInside statement member).mono larger⟩,
        fun frame member => (inside.2 frame member).mono larger⟩

end FormalSW.PyAst.HeapCalls.Relocation
