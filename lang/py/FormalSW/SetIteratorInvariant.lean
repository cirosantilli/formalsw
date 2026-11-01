import lang.py.FormalSW.SetIteratorRelocation

/-! Set fallback steps preserve the execution invariant used by later method steps. -/
namespace FormalSW.PyAst.SetCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation
open IteratorCalls.Relocation (relocateCore)
set_option Elab.async false

/-- Only transitions that expose a state or completion carry an observable heap. -/
def StepHeap (heap : Mutable.Heap) : Step SetCalls.State Mutable.Completion → Prop
  | .next state => state.core.heap = heap
  | .done (.ok completion) => completion.heap = heap
  | .done (.error _) | .unsupported => True

/-- A matching step retains layout, reference bounds, and every old address mapping.
Unsupported transitions have no resulting heap to constrain. -/
def Preserves (logical physical : Mutable.Heap) (rename : Nat → Nat) (anchors : Nat)
    (left right : Step SetCalls.State Mutable.Completion) : Prop :=
  ∃ logicalAfter physicalAfter nextMap,
    (∀ address < logical.length, nextMap address = rename address) ∧
    logical.length ≤ logicalAfter.length ∧ physical.length ≤ physicalAfter.length ∧
    ExecutionLayout logicalAfter physicalAfter nextMap ∧
    StepHeap logicalAfter left ∧ StepWithin left ∧
    right = relocateStep nextMap physicalAfter anchors left

theorem Preserves.unchanged {logical physical : Mutable.Heap} {rename : Nat → Nat} {anchors : Nat}
    {left right : Step SetCalls.State Mutable.Completion} (layout : ExecutionLayout logical physical rename)
    (heap : StepHeap logical left) (inside : StepWithin left)
    (paired : right = relocateStep rename physical anchors left) : Preserves logical physical rename anchors left right :=
  ⟨logical, physical, rename, fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _, layout, heap, inside, paired⟩

theorem Preserves.allocated {logical physical : Mutable.Heap} {rename : Nat → Nat} {anchors : Nat}
    {left right : Step SetCalls.State Mutable.Completion} (layout : ExecutionLayout logical physical rename)
    (collector : Mutable.Object) (notTuple : collector ≠ .tuple [])
    (collectorInside : ObjectWithin (logical.length + 1) collector)
    (heap : StepHeap (logical ++ [collector]) left) (inside : StepWithin left)
    (paired : right = relocateStep (extendMap rename logical.length physical.length)
      (physical ++ [relocateObject (extendMap rename logical.length physical.length) collector]) anchors left) :
    Preserves logical physical rename anchors left right :=
  ⟨logical ++ [collector], physical ++ [relocateObject (extendMap rename logical.length physical.length) collector],
    extendMap rename logical.length physical.length, extendMap_old rename logical.length physical.length,
    by simp, by simp, layout.append_object collector notTuple collectorInside, heap, inside, paired⟩

theorem comprehensionStart_heap (heap : Mutable.Heap) (target iterable : Expr) (body : List Stmt)
    (collector : Mutable.Object) (env : HeapCalls.Env) (address used : Nat) (stack : List HeapCalls.Frame) :
    StepHeap (heap ++ [collector]) (comprehensionStart target iterable body collector env address stack heap used) := by
  unfold comprehensionStart
  split <;> try trivial
  cases found : heap[address]? with
  | none => trivial
  | some object => cases object <;> trivial

theorem iterator_sequence_invariant (heap : Mutable.Heap) (choices : ChoiceSchedule)
    (anchors used address : Nat) (name : String) (body otherwise following : List Stmt)
    (env : HeapCalls.Env) (stack : List HeapCalls.Frame) (globals : Mutable.Globals)
    (inside : HeapCalls.Relocation.StateWithin
      ⟨.value (.ref address), .sequence name body otherwise following env :: stack, heap⟩) :
    let transition := iteratorStep choices anchors
      ⟨⟨.value (.ref address), .sequence name body otherwise following env :: stack, heap⟩, used⟩ globals
    StepHeap heap transition ∧ StepWithin transition := by
  dsimp only
  have saved := inside.2 _ (List.mem_cons_self ..)
  simp only [FrameWithin] at saved
  cases found : heap[address]? with
  | none => simp [iteratorStep, found, StepHeap, StepWithin]
  | some object =>
    cases object with
    | set items =>
      simp only [iteratorStep, found, StepHeap, StepWithin, HeapCalls.Relocation.StateWithin, WorkWithin]
      refine ⟨trivial, ⟨saved.1, ?_⟩, fun frame member => inside.2 frame (List.mem_cons_of_mem _ member)⟩
      intro statement member
      rcases List.mem_cons.mp member with rfl | member
      · simp only [StmtWithin]
        exact ⟨inside.1, saved.2.1, saved.2.2.1⟩
      · exact saved.2.2.2 statement member
    | _ => simp [iteratorStep, found, StepHeap, StepWithin]

theorem iterator_cursor_heap (heap : Mutable.Heap) (choices : ChoiceSchedule)
    (anchors used address : Nat) (name : String) (original remaining : List Constant)
    (body otherwise following : List Stmt) (env : HeapCalls.Env) (stack : List HeapCalls.Frame)
    (globals : Mutable.Globals) :
    StepHeap heap (iteratorStep choices anchors
      ⟨⟨.block (.setStepLoop name address original remaining body otherwise :: following) env, stack, heap⟩, used⟩ globals) := by
  cases found : heap[address]? with
  | none => simp [iteratorStep, found, StepHeap]
  | some object =>
    cases object with
    | set current =>
      simp only [iteratorStep, found]
      split
      · rfl
      · cases remaining with
        | nil => rfl
        | cons first rest =>
          cases (first :: rest)[choices used % (first :: rest).length]? <;> trivial
    | _ => simp [iteratorStep, found, StepHeap]

theorem comprehensionEnv_within (limit : Nat) (env : HeapCalls.Env) (generators : List (String × Expr × List Expr))
    (inside : EnvWithin limit env) : EnvWithin limit (comprehensionEnv env generators) := by
  intro name value found
  simp only [comprehensionEnv] at found
  split at found
  · cases found
  · exact inside name value found

theorem comprehensionTargetsEnv_within (limit : Nat) (env : HeapCalls.Env) (generators : List (Expr × Expr × List Expr))
    (inside : EnvWithin limit env) : EnvWithin limit (comprehensionTargetsEnv env generators) := by
  intro name value found
  simp only [comprehensionTargetsEnv] at found
  split at found
  · cases found
  · exact inside name value found

theorem sumInitial_value (heap after : Mutable.Heap) (value result : Mutable.Value)
    (executed : sumInitial value heap = some (.ok result, after)) : result = value := by
  cases value with
  | scalar value => cases value <;> simp_all [sumInitial, Mutable.error]
  | ref address =>
    cases found : heap[address]? with
    | none => simp [sumInitial, found, Mutable.unsupported] at executed
    | some object => cases object <;> simp_all [sumInitial, Mutable.error]

theorem sumEnter_invariant (heap : Mutable.Heap) (anchors used : Nat) (loop : Stmt)
    (env : HeapCalls.Env) (value : Mutable.Value) (stack : List HeapCalls.Frame) (globals : Mutable.Globals)
    (loopInside : StmtWithin heap.length loop) (envInside : EnvWithin heap.length env)
    (valueInside : value.edge.Within heap.length) (stackInside : ∀ frame ∈ stack, FrameWithin heap.length frame)
    (globalsInside : GlobalsWithin heap.length globals) :
    StepHeap heap (liftStep used (sumEnter anchors loop env value stack heap globals)) ∧
      StepWithin (liftStep used (sumEnter anchors loop env value stack heap globals)) := by
  cases tested : sumInitial value heap with
  | none => simp [sumEnter, run, tested, liftStep, StepHeap, StepWithin]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have unchanged := sumInitial_keeps_heap heap after value outcome valueInside tested
    subst after
    cases outcome with
    | error exception =>
      simp only [sumEnter, run, tested, done, liftStep, StepHeap, StepWithin, CompletionWithin]
      exact ⟨trivial, globalsInside, by intro _ impossible; cases impossible⟩
    | ok result =>
      have same := sumInitial_value heap heap value result tested
      subst result
      simp only [sumEnter, run, tested, liftStep, StepHeap, StepWithin, HeapCalls.Relocation.StateWithin, WorkWithin]
      refine ⟨trivial, ⟨envInside.setLocal _ value valueInside, ?_⟩, stackInside⟩
      simpa [StmtWithin] using loopInside

theorem iterator_sum_generator_invariant (heap : Mutable.Heap) (choices : ChoiceSchedule)
    (name : String) (element iterable start : Expr) (filters : List Expr) (generators : List (String × Expr × List Expr))
    (env : HeapCalls.Env) (address used anchors : Nat) (stack : List HeapCalls.Frame) (globals : Mutable.Globals)
    (addressInside : address < heap.length) (envInside : EnvWithin heap.length env)
    (stackInside : ∀ frame ∈ stack, FrameWithin heap.length frame) :
    let transition := iteratorStep choices anchors
      ⟨⟨.operation (.sumGenerator element ((name, iterable, filters) :: generators) env start)
        [.ref address], stack, heap⟩, used⟩ globals
    StepHeap heap transition ∧ StepWithin transition := by
  dsimp only
  simp only [iteratorStep]
  split <;> try trivial
  cases found : heap[address]? with
  | none => trivial
  | some object =>
    cases object <;> try trivial
    simp only [StepHeap, StepWithin, HeapCalls.Relocation.StateWithin, WorkWithin]
    refine ⟨trivial, envInside, ?_⟩
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simp only [FrameWithin, StmtWithin]
      refine ⟨comprehensionEnv_within heap.length env _ envInside, addressInside, ?_, by simp⟩
      exact fun statement member => (comprehensionFilters_within 0 filters _ (sumBody_source element generators) statement member).mono (Nat.zero_le _)
    · exact stackInside frame member

theorem iterator_extremum_generator_invariant (heap : Mutable.Heap) (choices : ChoiceSchedule)
    (target : Expr) (maximum : Bool) (fallback : Option Expr) (element iterable : Expr) (filters : List Expr)
    (generators : List (Expr × Expr × List Expr)) (env : HeapCalls.Env)
    (address used anchors : Nat) (stack : List HeapCalls.Frame) (globals : Mutable.Globals)
    (addressInside : address < heap.length) (envInside : EnvWithin heap.length env)
    (stackInside : ∀ frame ∈ stack, FrameWithin heap.length frame) :
    let transition := iteratorStep choices anchors
      ⟨⟨.operation (.extremumGenerator maximum fallback element ((target, iterable, filters) :: generators) env)
        [.ref address], stack, heap⟩, used⟩ globals
    StepHeap heap transition ∧ StepWithin transition := by
  dsimp only
  simp only [iteratorStep]
  split <;> try trivial
  cases found : heap[address]? with
  | none => trivial
  | some object =>
    cases object <;> try trivial
    simp only [StepHeap, StepWithin, HeapCalls.Relocation.StateWithin, WorkWithin]
    refine ⟨trivial, envInside, ?_⟩
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simp only [FrameWithin, StmtWithin]
      refine ⟨comprehensionTargetsEnv_within heap.length env _ envInside, addressInside, ?_, by simp⟩
      have body := comprehensionTargetBody_within 0 target _ (comprehensionFilters_within 0 filters _
        (comprehensionTargetsBody_within 0 _ generators (extremumBody_source maximum element)))
      exact fun statement member => (body statement member).mono (Nat.zero_le _)
    · exact stackInside frame member

theorem iterator_sum_sequence_invariant (heap : Mutable.Heap) (choices : ChoiceSchedule)
    (address used anchors : Nat) (value : Mutable.Value) (stack : List HeapCalls.Frame) (globals : Mutable.Globals)
    (addressInside : address < heap.length) (valueInside : value.edge.Within heap.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin heap.length frame) (globalsInside : GlobalsWithin heap.length globals) :
    let transition := iteratorStep choices anchors ⟨⟨.operation .sumSequence [.ref address, value], stack, heap⟩, used⟩ globals
    StepHeap heap transition ∧ StepWithin transition := by
  dsimp only
  simp only [iteratorStep]
  cases found : heap[address]? with
  | none => trivial
  | some object =>
    cases object <;> try trivial
    apply sumEnter_invariant heap anchors used _ (fun _ => none) value stack globals _ _ valueInside stackInside globalsInside
    · simp only [StmtWithin]
      exact ⟨addressInside, fun statement member => (sumBody_source (.name sumItem) [] statement member).mono (Nat.zero_le _), by simp⟩
    · intro _ _ impossible; cases impossible

theorem iterator_list_comprehension_preserves {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (choices : ChoiceSchedule) (name : String)
    (element iterable : Expr) (filters : List Expr) (generators : List (String × Expr × List Expr))
    (env : HeapCalls.Env) (address used logicalAnchors physicalAnchors : Nat) (stack : List HeapCalls.Frame)
    (globals : Mutable.Globals) (addressInside : address < logical.length) (envInside : EnvWithin logical.length env)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) :
    Preserves logical physical rename physicalAnchors
      (iteratorStep choices logicalAnchors ⟨⟨.operation (.comprehension element ((name, iterable, filters) :: generators) env) [.ref address], stack, logical⟩, used⟩ globals)
      (iteratorStep choices physicalAnchors
        (relocateCore rename physical ⟨⟨.operation (.comprehension element ((name, iterable, filters) :: generators) env) [.ref address], stack, logical⟩, used⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.allocated layout (.list []) (by simp) (by simp [ObjectWithin, objectValues])
  · exact comprehensionStart_heap logical (.name name) iterable _ (.list []) env address used stack
  · exact comprehensionStart_within logical (.name name) iterable _ (.list []) env address used stack addressInside envInside
      (comprehensionFilters_within (logical.length + 1) filters _ (comprehensionBody_within (logical.length + 1) logical.length element generators (by omega))) stackInside
  · simpa only [relocateObject, List.map_nil] using iterator_list_comprehension_relocates layout.runtime choices name
      element iterable filters generators env address used logicalAnchors physicalAnchors stack globals addressInside envInside stackInside

theorem iterator_targets_comprehension_preserves {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (choices : ChoiceSchedule) (target : Expr)
    (element iterable : Expr) (filters : List Expr) (generators : List (Expr × Expr × List Expr))
    (env : HeapCalls.Env) (address used logicalAnchors physicalAnchors : Nat) (stack : List HeapCalls.Frame)
    (globals : Mutable.Globals) (addressInside : address < logical.length) (envInside : EnvWithin logical.length env)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) :
    Preserves logical physical rename physicalAnchors
      (iteratorStep choices logicalAnchors ⟨⟨.operation (.comprehensionTargets element ((target, iterable, filters) :: generators) env) [.ref address], stack, logical⟩, used⟩ globals)
      (iteratorStep choices physicalAnchors
        (relocateCore rename physical ⟨⟨.operation (.comprehensionTargets element ((target, iterable, filters) :: generators) env) [.ref address], stack, logical⟩, used⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.allocated layout (.list []) (by simp) (by simp [ObjectWithin, objectValues])
  · exact comprehensionStart_heap logical target iterable _ (.list []) env address used stack
  · exact comprehensionStart_within logical target iterable _ (.list []) env address used stack addressInside envInside
      (comprehensionFilters_within (logical.length + 1) filters _ (comprehensionTargetsBody_within (logical.length + 1) _ generators (by simp [StmtWithin]))) stackInside
  · simpa only [relocateObject, List.map_nil] using iterator_targets_comprehension_relocates layout.runtime choices target
      element iterable filters generators env address used logicalAnchors physicalAnchors stack globals addressInside envInside stackInside

theorem iterator_set_comprehension_preserves {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (choices : ChoiceSchedule) (target : Expr)
    (element iterable : Expr) (filters : List Expr) (generators : List (Expr × Expr × List Expr))
    (env : HeapCalls.Env) (address used logicalAnchors physicalAnchors : Nat) (stack : List HeapCalls.Frame)
    (globals : Mutable.Globals) (addressInside : address < logical.length) (envInside : EnvWithin logical.length env)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) :
    Preserves logical physical rename physicalAnchors
      (iteratorStep choices logicalAnchors ⟨⟨.operation (.setComprehension element ((target, iterable, filters) :: generators) env) [.ref address], stack, logical⟩, used⟩ globals)
      (iteratorStep choices physicalAnchors
        (relocateCore rename physical ⟨⟨.operation (.setComprehension element ((target, iterable, filters) :: generators) env) [.ref address], stack, logical⟩, used⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.allocated layout (.set []) (by simp) (by simp [ObjectWithin, objectValues])
  · exact comprehensionStart_heap logical target iterable _ (.set []) env address used stack
  · exact comprehensionStart_within logical target iterable _ (.set []) env address used stack addressInside envInside
      (comprehensionFilters_within (logical.length + 1) filters _ (comprehensionTargetsBody_within (logical.length + 1) _ generators (by simp [StmtWithin]))) stackInside
  · simpa only [relocateObject, List.map_nil] using iterator_set_comprehension_relocates layout.runtime choices target
      element iterable filters generators env address used logicalAnchors physicalAnchors stack globals addressInside envInside stackInside

theorem iterator_dict_comprehension_preserves {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (choices : ChoiceSchedule) (target key : Expr)
    (element iterable : Expr) (filters : List Expr) (generators : List (Expr × Expr × List Expr))
    (env : HeapCalls.Env) (address used logicalAnchors physicalAnchors : Nat) (stack : List HeapCalls.Frame)
    (globals : Mutable.Globals) (addressInside : address < logical.length) (envInside : EnvWithin logical.length env)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) :
    Preserves logical physical rename physicalAnchors
      (iteratorStep choices logicalAnchors ⟨⟨.operation (.dictionaryComprehension key element ((target, iterable, filters) :: generators) env) [.ref address], stack, logical⟩, used⟩ globals)
      (iteratorStep choices physicalAnchors
        (relocateCore rename physical ⟨⟨.operation (.dictionaryComprehension key element ((target, iterable, filters) :: generators) env) [.ref address], stack, logical⟩, used⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.allocated layout (.dict []) (by simp) (by simp [ObjectWithin, objectValues])
  · exact comprehensionStart_heap logical target iterable _ (.dict []) env address used stack
  · exact comprehensionStart_within logical target iterable _ (.dict []) env address used stack addressInside envInside
      (comprehensionFilters_within (logical.length + 1) filters _ (comprehensionTargetsBody_within (logical.length + 1) _ generators (by simp [StmtWithin]))) stackInside
  · simpa only [relocateObject, List.map_nil] using iterator_dict_comprehension_relocates layout.runtime choices target key
      element iterable filters generators env address used logicalAnchors physicalAnchors stack globals addressInside envInside stackInside

/-- Every modeled fallback preserves the invariant needed by the next interpreter step. -/
theorem iteratorStep_preserves (choices : ChoiceSchedule) (core : SetCalls.State)
    (physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (globals : Mutable.Globals) (layout : ExecutionLayout core.core.heap physical rename)
    (inside : HeapCalls.Relocation.StateWithin core.core) (globalsInside : GlobalsWithin core.core.heap.length globals) :
    Preserves core.core.heap physical rename physicalAnchors (iteratorStep choices logicalAnchors core globals)
      (iteratorStep choices physicalAnchors (relocateCore rename physical core) (relocateGlobals rename globals)) := by
  rcases core with ⟨⟨work, stack, logical⟩, used⟩
  have unchanged
      (invariant : StepHeap logical (iteratorStep choices logicalAnchors ⟨⟨work, stack, logical⟩, used⟩ globals) ∧
        StepWithin (iteratorStep choices logicalAnchors ⟨⟨work, stack, logical⟩, used⟩ globals))
      (paired : iteratorStep choices physicalAnchors (relocateCore rename physical ⟨⟨work, stack, logical⟩, used⟩)
        (relocateGlobals rename globals) = relocateStep rename physical physicalAnchors
          (iteratorStep choices logicalAnchors ⟨⟨work, stack, logical⟩, used⟩ globals)) :=
    Preserves.unchanged layout invariant.1 invariant.2 paired
  have unsupported
      (left : iteratorStep choices logicalAnchors ⟨⟨work, stack, logical⟩, used⟩ globals = .unsupported)
      (right : iteratorStep choices physicalAnchors (relocateCore rename physical ⟨⟨work, stack, logical⟩, used⟩)
        (relocateGlobals rename globals) = .unsupported) :=
    unchanged (by simp [left, StepHeap, StepWithin]) (by simp [left, right, relocateStep, Step.map])
  cases work with
  | value value =>
    cases value with
    | scalar value => exact unsupported rfl rfl
    | ref address =>
      cases stack with
      | nil => exact unsupported rfl rfl
      | cons frame stack =>
        cases frame with
        | sequence name body otherwise following env =>
          exact unchanged (iterator_sequence_invariant logical choices logicalAnchors used address name body otherwise following env stack globals inside)
            (iterator_sequence_relocates layout.runtime choices logicalAnchors physicalAnchors used address name body otherwise following env stack globals inside.1)
        | _ =>
          apply unsupported <;> simp [relocateCore, HeapCalls.Relocation.relocateState, relocateWork, relocateValue, relocateFrame, iteratorStep]
  | block statements env =>
    cases statements with
    | nil => exact unsupported rfl rfl
    | cons statement following =>
      cases statement with
      | setStepLoop name address original remaining body otherwise =>
        have cursorInside := inside.1.2 _ (List.mem_cons_self ..)
        simp only [StmtWithin] at cursorInside
        exact unchanged
          ⟨iterator_cursor_heap logical choices logicalAnchors used address name original remaining body otherwise following env stack globals,
            iterator_cursor_within logical choices logicalAnchors used address name original remaining body otherwise following env stack globals inside globalsInside⟩
          (iterator_cursor_relocates layout.runtime choices logicalAnchors physicalAnchors used address name original remaining body otherwise following env stack globals cursorInside.1)
      | _ =>
        apply unsupported <;> simp [relocateCore, HeapCalls.Relocation.relocateState, relocateWork, relocateStmt, iteratorStep]
  | operation operation values =>
    cases operation with
    | comprehension element generators env | comprehensionTargets element generators env
    | setComprehension element generators env | dictionaryComprehension key element generators env
    | sumGenerator element generators env start | extremumGenerator maximum fallback element generators env =>
      cases generators with
      | nil => exact unsupported rfl rfl
      | cons generator generators =>
        rcases generator with ⟨target, iterable, filters⟩
        cases values with
        | nil => exact unsupported rfl rfl
        | cons value values =>
          cases values with
          | cons => cases value <;> exact unsupported rfl rfl
          | nil =>
            cases value with
            | scalar value => exact unsupported rfl rfl
            | ref address =>
              have addressInside := inside.1.2 (.ref address) (List.mem_cons_self ..)
              first
                | exact iterator_list_comprehension_preserves layout choices target element iterable filters generators env
                    address used logicalAnchors physicalAnchors stack globals addressInside inside.1.1 inside.2
                | exact iterator_targets_comprehension_preserves layout choices target element iterable filters generators env
                    address used logicalAnchors physicalAnchors stack globals addressInside inside.1.1 inside.2
                | exact iterator_set_comprehension_preserves layout choices target element iterable filters generators env
                    address used logicalAnchors physicalAnchors stack globals addressInside inside.1.1 inside.2
                | exact iterator_dict_comprehension_preserves layout choices target key element iterable filters generators env
                    address used logicalAnchors physicalAnchors stack globals addressInside inside.1.1 inside.2
                | exact unchanged
                    (iterator_sum_generator_invariant logical choices target element iterable start filters generators env address used logicalAnchors stack globals addressInside inside.1.1 inside.2)
                    (iterator_sum_generator_relocates layout.runtime choices target element iterable start filters generators env address used logicalAnchors physicalAnchors stack globals addressInside)
                | exact unchanged
                    (iterator_extremum_generator_invariant logical choices target maximum fallback element iterable filters generators env address used logicalAnchors stack globals addressInside inside.1.1 inside.2)
                    (iterator_extremum_generator_relocates layout.runtime choices target maximum fallback element iterable filters generators env address used logicalAnchors physicalAnchors stack globals addressInside)
    | sumSequence =>
      cases values with
      | nil => exact unsupported rfl rfl
      | cons value values =>
        cases value with
        | scalar value => exact unsupported rfl rfl
        | ref address =>
          cases values with
          | nil => exact unsupported rfl rfl
          | cons start values =>
            cases values with
            | cons => exact unsupported rfl rfl
            | nil =>
              exact unchanged
                (iterator_sum_sequence_invariant logical choices address used logicalAnchors start stack globals
                  (inside.1.2 (.ref address) (by simp)) (inside.1.2 start (by simp)) inside.2 globalsInside)
                (iterator_sum_sequence_relocates layout.runtime choices address used logicalAnchors physicalAnchors start stack globals
                  (inside.1.2 (.ref address) (by simp)) (inside.1.2 start (by simp)))
    | _ =>
      apply unsupported <;> simp [relocateCore, HeapCalls.Relocation.relocateState, relocateWork, relocateRuntimeOperation, relocateOperation, iteratorStep]
  | _ =>
    apply unsupported <;> simp [relocateCore, HeapCalls.Relocation.relocateState, relocateWork, iteratorStep]

/-- Expose the actual next state and retain the fixed global roots across map growth. -/
theorem Preserves.next {logical physical : Mutable.Heap} {rename : Nat → Nat} {anchors : Nat}
    {next : SetCalls.State} {right : Step SetCalls.State Mutable.Completion}
    (preserved : Preserves logical physical rename anchors (.next next) right)
    (globals : Mutable.Globals) (globalsInside : GlobalsWithin logical.length globals) :
    ∃ physicalAfter nextMap,
      (∀ address < logical.length, nextMap address = rename address) ∧
      logical.length ≤ next.core.heap.length ∧ physical.length ≤ physicalAfter.length ∧
      ExecutionLayout next.core.heap physicalAfter nextMap ∧ HeapCalls.Relocation.StateWithin next.core ∧
      GlobalsWithin next.core.heap.length globals ∧ relocateGlobals nextMap globals = relocateGlobals rename globals ∧
      right = .next (relocateCore nextMap physicalAfter next) := by
  obtain ⟨logicalAfter, physicalAfter, nextMap, agree, grows, physicalGrows, layout, heap, inside, paired⟩ := preserved
  have same : next.core.heap = logicalAfter := heap
  subst logicalAfter
  exact ⟨physicalAfter, nextMap, agree, grows, physicalGrows, layout, inside,
    globalsInside.mono grows, relocateGlobals_congr nextMap rename logical.length globals agree globalsInside, paired⟩

/-- Later steps still preserve the roots that existed before an earlier allocation. -/
theorem Preserves.rebase {logical physical middleLogical middlePhysical : Mutable.Heap}
    {rename middleMap : Nat → Nat} {anchors : Nat} {left right : Step SetCalls.State Mutable.Completion}
    (preserved : Preserves middleLogical middlePhysical middleMap anchors left right)
    (agree : ∀ address < logical.length, middleMap address = rename address)
    (grows : logical.length ≤ middleLogical.length) (physicalGrows : physical.length ≤ middlePhysical.length) :
    Preserves logical physical rename anchors left right := by
  obtain ⟨logicalAfter, physicalAfter, nextMap, nextAgree, nextGrows, physicalNextGrows, layout, heap, inside, paired⟩ := preserved
  refine ⟨logicalAfter, physicalAfter, nextMap, ?_, Nat.le_trans grows nextGrows, Nat.le_trans physicalGrows physicalNextGrows,
    layout, heap, inside, paired⟩
  intro address bounded
  exact (nextAgree address (Nat.lt_of_lt_of_le bounded grows)).trans (agree address bounded)

/-- The modeled fallback can replace a paired unsupported heap step without losing invariants. -/
theorem step_fallback_preserves (module : Module) (choices : ChoiceSchedule) (core : SetCalls.State)
    (physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (globals : Mutable.Globals) (layout : ExecutionLayout core.core.heap physical rename)
    (inside : HeapCalls.Relocation.StateWithin core.core) (globalsInside : GlobalsWithin core.core.heap.length globals)
    (fallback : HeapCalls.step module logicalAnchors core.core globals = .unsupported)
    (otherFallback : HeapCalls.step module physicalAnchors (HeapCalls.Relocation.relocateState rename physical core.core)
      (relocateGlobals rename globals) = .unsupported) :
    Preserves core.core.heap physical rename physicalAnchors (SetCalls.step module logicalAnchors choices core globals)
      (SetCalls.step module physicalAnchors choices (relocateCore rename physical core) (relocateGlobals rename globals)) := by
  simpa only [SetCalls.step, fallback, relocateCore, otherFallback] using
    iteratorStep_preserves choices core physical rename logicalAnchors physicalAnchors globals layout inside globalsInside

end FormalSW.PyAst.SetCalls.Relocation
