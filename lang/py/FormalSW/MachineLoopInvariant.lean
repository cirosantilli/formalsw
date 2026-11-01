import lang.py.FormalSW.MachineMutationInvariant

/-! Loop transfers preserve the invariant used to compose iterator executions. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem run_readonly_heap {α : Type} (heap : Mutable.Heap) (anchors : Nat)
    (action : Mutable.Eval α) (globals : Mutable.Globals)
    (readonly : ∀ outcome after, action heap = some (outcome, after) → after = heap)
    (next : α → Mutable.Heap → Step State Mutable.Completion)
    (retained : ∀ value, action heap = some (.ok value, heap) → StepHeap heap (next value heap)) :
    StepHeap heap (run (globals := globals) anchors heap action next) := by
  cases executed : action heap with
  | none => simp [run, executed, StepHeap]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have same := readonly outcome after executed
    subst after
    cases outcome with
    | error exception => simp [run, executed, done, StepHeap]
    | ok value => simpa only [run, executed] using retained value executed

variable (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
  (logicalAnchors physicalAnchors : Nat)

theorem step_while_preserves (condition : Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.block (.whileDo condition body otherwise :: following) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.whileDo condition body otherwise :: following) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.block (.whileDo condition body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · exact rfl
  · exact StateWithin.while_loop module logical logicalAnchors condition body otherwise following env stack globals inside
  · exact step_while_relocates module logical physical rename logicalAnchors physicalAnchors
      condition body otherwise following env stack globals

theorem step_range_loop_preserves (name : String) (next stop stride : Int) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.block (.rangeStepLoop name next stop stride body otherwise :: following) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.rangeStepLoop name next stop stride body otherwise :: following) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.block (.rangeStepLoop name next stop stride body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · cases tested : Calls.rangeContinues next stop stride <;> simp [step, tested, StepHeap]
  · exact StateWithin.range_loop module logical logicalAnchors name next stop stride body otherwise following env stack globals inside
  · exact step_range_loop_relocates module logical physical rename logicalAnchors physicalAnchors
      name next stop stride body otherwise following env stack globals

theorem step_loopResume_preserves (next : Stmt) (following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.block (.loopResume next :: following) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.loopResume next :: following) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.block (.loopResume next :: following) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · exact rfl
  · exact StateWithin.loopResume module logical logicalAnchors next following env stack globals inside
  · exact step_loopResume_relocates module logical physical rename logicalAnchors physicalAnchors
      next following env stack globals

theorem step_break_preserves (following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.block (.breakLoop :: following) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.breakLoop :: following) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.block (.breakLoop :: following) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · cases target : Calls.loopTarget following with
    | none => simp [step, target, protectGenerator, StepHeap]
    | some pair => rcases pair with ⟨next, rest⟩; simp [step, target, StepHeap]
  · exact StateWithin.break_loop module logical logicalAnchors following env stack globals inside
  · exact step_break_relocates module logical physical rename logicalAnchors physicalAnchors
      following env stack globals

theorem step_continue_preserves (following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.block (.continueLoop :: following) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.continueLoop :: following) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.block (.continueLoop :: following) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · cases target : Calls.loopTarget following with
    | none => simp [step, target, protectGenerator, StepHeap]
    | some pair => rcases pair with ⟨next, rest⟩; simp [step, target, StepHeap]
  · exact StateWithin.continue_loop module logical logicalAnchors following env stack globals inside
  · exact step_continue_relocates module logical physical rename logicalAnchors physicalAnchors
      following env stack globals

theorem step_sequence_loop_preserves
    (name : String) (source : SequenceSource) (position : Nat) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.block (.sequenceStepLoop name source position body otherwise :: following) env, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.sequenceStepLoop name source position body otherwise :: following) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.block (.sequenceStepLoop name source position body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · apply protectGenerator_heap
    apply run_readonly_heap
    · exact fun outcome after executed => sequence_keeps_heap logical after (sequenceValue source) outcome executed
    · intro items _
      cases items[position]? <;> rfl
  · exact StateWithin.sequence_loop module logical logicalAnchors layout.closed
      name source position body otherwise following env stack globals globalsInside inside
  · have loopInside := inside.1.2 _ (List.mem_cons_self ..)
    simp only [StmtWithin] at loopInside
    exact step_sequence_loop_relocates module logical physical rename logicalAnchors physicalAnchors layout.runtime
      name source position body otherwise following env stack globals
      loopInside.1

theorem step_reverse_loop_preserves (name : String) (source : SequenceSource) (position : Int) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.block (.reverseSequenceStepLoop name source position body otherwise :: following) env, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.reverseSequenceStepLoop name source position body otherwise :: following) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.block (.reverseSequenceStepLoop name source position body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · apply protectGenerator_heap
    by_cases finished : position < 0
    · simp [finished, StepHeap]
    · simp only [finished, if_false]
      apply run_readonly_heap
      · exact fun outcome after executed => reversibleSequence_keeps_heap logical after (sequenceValue source) outcome executed
      · intro items _
        cases items[position.toNat]? <;> rfl
  · exact StateWithin.reverse_loop module logical logicalAnchors layout.closed
      name source position body otherwise following env stack globals globalsInside inside
  · have loopInside := inside.1.2 _ (List.mem_cons_self ..)
    simp only [StmtWithin] at loopInside
    exact step_reverse_loop_relocates module logical physical rename logicalAnchors physicalAnchors layout.runtime
      name source position body otherwise following env stack globals loopInside.1

theorem step_enumerate_loop_preserves (index name : String) (source : SequenceSource) (position : Nat) (counter : Int) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.block (.enumerateStepLoop index name source position counter body otherwise :: following) env, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.enumerateStepLoop index name source position counter body otherwise :: following) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.block (.enumerateStepLoop index name source position counter body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · apply protectGenerator_heap
    apply run_readonly_heap
    · exact fun outcome after executed => sequence_keeps_heap logical after (sequenceValue source) outcome executed
    · intro items _
      cases items[position]? <;> rfl
  · exact StateWithin.enumerate_loop module logical logicalAnchors layout.closed
      index name source position counter body otherwise following env stack globals globalsInside inside
  · have loopInside := inside.1.2 _ (List.mem_cons_self ..)
    simp only [StmtWithin] at loopInside
    exact step_enumerate_loop_relocates module logical physical rename logicalAnchors physicalAnchors layout.runtime
      index name source position counter body otherwise following env stack globals loopInside.1

theorem step_unpack_loop_preserves (names : List String) (source : SequenceSource) (position : Nat) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.block (.unpackStepLoop names source position body otherwise :: following) env, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.unpackStepLoop names source position body otherwise :: following) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.block (.unpackStepLoop names source position body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · apply protectGenerator_heap
    apply run_readonly_heap
    · exact fun outcome after executed => sequence_keeps_heap logical after (sequenceValue source) outcome executed
    · intro items _
      cases item : items[position]? with
      | none => rfl
      | some value =>
        apply run_readonly_heap
        · exact fun outcome after executed => sequence_keeps_heap logical after value outcome executed
        · intro fields _
          split <;> rfl
  · exact StateWithin.unpack_loop module logical logicalAnchors layout.closed
      names source position body otherwise following env stack globals globalsInside inside
  · have loopInside := inside.1.2 _ (List.mem_cons_self ..)
    simp only [StmtWithin] at loopInside
    exact step_unpack_loop_relocates module logical physical rename logicalAnchors physicalAnchors layout.runtime layout.closed
      names source position body otherwise following env stack globals loopInside.1

theorem step_range_start_preserves (name : String) (values : List Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.startRange name values body otherwise following env, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.startRange name values body otherwise following env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.startRange name values body otherwise following env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · apply protectGenerator_heap
    cases tested : rangeBounds values with
    | error exception => simp [tested, done, StepHeap]
    | ok triple => rcases triple with ⟨start, stop, stride⟩; simp [tested, StepHeap]
  · exact StateWithin.range_start module logical logicalAnchors name values body otherwise following env stack globals globalsInside inside
  · exact step_range_start_relocates module logical physical rename logicalAnchors physicalAnchors
      name values body otherwise following env stack globals

theorem step_range_arguments_preserves (name : String) (value : Value) (done : List Value) (rest : List Expr)
    (body otherwise following : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .rangeArguments name done rest body otherwise following env :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .rangeArguments name done rest body otherwise following env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .rangeArguments name done rest body otherwise following env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · cases rest <;> rfl
  · exact StateWithin.range_arguments module logical logicalAnchors name value done rest body otherwise following env stack globals inside
  · exact step_range_arguments_relocates module logical physical rename logicalAnchors physicalAnchors
      name value done rest body otherwise following env stack globals

theorem step_sequence_start_preserves (name : String) (value : Value) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .sequence name body otherwise following env :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .sequence name body otherwise following env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value value, .sequence name body otherwise following env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · apply protectGenerator_heap
    apply run_readonly_heap
    · exact fun outcome after executed => sequence_keeps_heap logical after value outcome executed
    · intro _ _; rfl
  · exact StateWithin.sequence_start module logical logicalAnchors name value body otherwise following env stack globals globalsInside inside
  · exact step_sequence_start_relocates module logical physical rename logicalAnchors physicalAnchors layout.runtime
      name value body otherwise following env stack globals inside.1

theorem step_for_heap (target iterable : Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    StepHeap logical
      (step module logicalAnchors ⟨.block (.forIn target iterable body otherwise :: following) env, stack, logical⟩ globals) := by
  have unpack (asList : Bool) (targets : List Expr) :
      StepHeap logical (step module logicalAnchors
        ⟨.block (.forIn (if asList then .list targets else .tuple targets) iterable body otherwise :: following) env, stack, logical⟩ globals) := by
    rw [step_for_unpack_dispatch]
    split
    · rfl
    · exact argumentsState_heap ..
    · exact argumentsState_heap ..
    · split
      · rfl
      · rfl
      · split <;> trivial
  have other (target : Expr) (notFlat : flatForTarget target = false) :
      StepHeap logical (step module logicalAnchors
        ⟨.block (.forIn target iterable body otherwise :: following) env, stack, logical⟩ globals) := by
    rw [step_for_other_dispatch module logical logicalAnchors target iterable notFlat]
    split
    · rfl
    · exact argumentsState_heap ..
    · exact argumentsState_heap ..
    · trivial
  cases target with
  | name name =>
    rw [step_for_name_dispatch]
    split
    · rfl
    · exact argumentsState_heap ..
    · exact argumentsState_heap ..
    · split <;> rfl
    · rfl
  | tuple targets => exact unpack false targets
  | list targets => exact unpack true targets
  | _ => exact other _ rfl

/-- Source for-loop entry covers every target and iterable shape, including unsupported dispatch. -/
theorem step_for_preserves (target iterable : Expr) (body otherwise following : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.block (.forIn target iterable body otherwise :: following) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.forIn target iterable body otherwise :: following) env, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.block (.forIn target iterable body otherwise :: following) env, stack, logical⟩)
        (relocateGlobals rename globals)) :=
  Preserves.unchanged layout (step_for_heap module logical logicalAnchors target iterable body otherwise following env stack globals)
    (StateWithin.forIn module logical logicalAnchors target iterable body otherwise following env stack globals inside)
    (step_for_relocates module logical physical rename logicalAnchors physicalAnchors target iterable body otherwise following env stack globals)

end FormalSW.PyAst.HeapCalls.Relocation

