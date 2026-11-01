import lang.py.FormalSW.IteratorCore

/-! Set traversal preserves scheduled choices and live cursor references across layouts. -/
namespace FormalSW.PyAst.SetCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation
open IteratorCalls.Relocation (relocateCore)
set_option Elab.async false

def relocateStep (rename : Nat → Nat) (physical : Mutable.Heap) (anchors : Nat)
    (transition : Step SetCalls.State Mutable.Completion) : Step SetCalls.State Mutable.Completion :=
  transition.map (relocateCore rename physical) (relocateCompletion rename physical anchors)

def StepWithin : Step SetCalls.State Mutable.Completion → Prop
  | .next state => HeapCalls.Relocation.StateWithin state.core
  | .done (.ok completion) => CompletionWithin completion
  | .done (.error _) | .unsupported => True

theorem iterator_sequence_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (choices : ChoiceSchedule)
    (logicalAnchors physicalAnchors used address : Nat) (name : String) (body otherwise following : List Stmt)
    (env : HeapCalls.Env) (stack : List HeapCalls.Frame) (globals : Mutable.Globals)
    (inside : address < logical.length) :
    iteratorStep choices physicalAnchors
      (relocateCore rename physical ⟨⟨.value (.ref address), .sequence name body otherwise following env :: stack, logical⟩, used⟩)
      (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors (iteratorStep choices logicalAnchors
        ⟨⟨.value (.ref address), .sequence name body otherwise following env :: stack, logical⟩, used⟩ globals) := by
  have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
  have moved := layout.lookup address _ found
  cases object : logical[address] <;>
    simp [iteratorStep, relocateCore, HeapCalls.Relocation.relocateState, relocateWork, relocateValue,
      relocateFrame, found, object, relocateObject] at moved ⊢ <;>
    simp [moved, relocateStep, Step.map, relocateCore, HeapCalls.Relocation.relocateState, relocateWork, relocateStmt]

theorem iterator_cursor_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (choices : ChoiceSchedule)
    (logicalAnchors physicalAnchors used address : Nat) (name : String) (original remaining : List Constant)
    (body otherwise following : List Stmt) (env : HeapCalls.Env) (stack : List HeapCalls.Frame)
    (globals : Mutable.Globals) (inside : address < logical.length) :
    iteratorStep choices physicalAnchors
      (relocateCore rename physical ⟨⟨.block
        (.setStepLoop name address original remaining body otherwise :: following) env, stack, logical⟩, used⟩)
      (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors (iteratorStep choices logicalAnchors
        ⟨⟨.block (.setStepLoop name address original remaining body otherwise :: following) env, stack, logical⟩, used⟩ globals) := by
  have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
  have moved := layout.lookup address _ found
  cases object : logical[address] with
  | set current =>
    simp only [object, relocateObject] at moved
    simp only [relocateCore, HeapCalls.Relocation.relocateState, relocateWork, List.map_cons, relocateStmt,
      iteratorStep, found, object, moved]
    by_cases changed : current.length != original.length
    · simp [changed, liftStep, done, relocateStep, Step.map, relocateCompletion, Except.map]
    · simp only [changed, Bool.false_eq_true, if_false]
      cases remaining with
      | nil => simp [relocateStep, Step.map, relocateCore, HeapCalls.Relocation.relocateState, relocateWork]
      | cons first rest =>
        cases selected : (first :: rest)[choices used % (first :: rest).length]? with
        | none => simp [relocateStep, Step.map]
        | some item =>
          simp [relocateStep, Step.map, relocateCore, HeapCalls.Relocation.relocateState,
            relocateWork, relocateEnv_set, ← loopContinuation_relocate, relocateStmt, relocateValue]
  | _ =>
    simp [object, relocateObject] at moved
    simp [relocateCore, HeapCalls.Relocation.relocateState, relocateWork, relocateStmt,
      iteratorStep, found, object, moved, relocateStep, Step.map]

theorem iterator_cursor_within (heap : Mutable.Heap) (choices : ChoiceSchedule)
    (anchors used address : Nat) (name : String) (original remaining : List Constant)
    (body otherwise following : List Stmt) (env : HeapCalls.Env) (stack : List HeapCalls.Frame)
    (globals : Mutable.Globals)
    (inside : HeapCalls.Relocation.StateWithin
      ⟨.block (.setStepLoop name address original remaining body otherwise :: following) env, stack, heap⟩)
    (globalsInside : GlobalsWithin heap.length globals) :
    StepWithin (iteratorStep choices anchors
      ⟨⟨.block (.setStepLoop name address original remaining body otherwise :: following) env, stack, heap⟩, used⟩ globals) := by
  have cursorInside := inside.1.2 _ (List.mem_cons_self ..)
  simp only [StmtWithin] at cursorInside
  have followingInside : ∀ statement ∈ following, StmtWithin heap.length statement :=
    fun statement member => inside.1.2 statement (List.mem_cons_of_mem _ member)
  cases found : heap[address]? with
  | none => simp [iteratorStep, found, StepWithin]
  | some object =>
    cases object with
    | set current =>
      by_cases changed : current.length != original.length
      · simp only [iteratorStep, found, changed, if_true, liftStep, done, StepWithin, CompletionWithin]
        exact ⟨globalsInside, by intro _ impossible; cases impossible⟩
      · simp only [iteratorStep, found, changed, Bool.false_eq_true, if_false]
        cases remaining with
        | nil =>
          simp only [StepWithin, HeapCalls.Relocation.StateWithin, WorkWithin]
          exact ⟨⟨inside.1.1, fun statement member => (List.mem_append.mp member).elim
            (cursorInside.2.2 statement) (followingInside statement)⟩, inside.2⟩
        | cons first rest =>
          cases selected : (first :: rest)[choices used % (first :: rest).length]? with
          | none => simp [StepWithin]
          | some item =>
            simp only [StepWithin, HeapCalls.Relocation.StateWithin, WorkWithin]
            refine ⟨⟨inside.1.1.setLocal name (.scalar item) trivial, ?_⟩, inside.2⟩
            intro statement member
            rcases List.mem_append.mp member with member | member
            · rcases List.mem_append.mp member with member | member
              · exact cursorInside.2.1 statement member
              · have same := List.mem_singleton.mp member
                subst statement
                apply loopContinuation_within
                simp only [StmtWithin]
                exact cursorInside
            · exact followingInside statement member
    | _ => simp [iteratorStep, found, StepWithin]

theorem comprehensionFilters_relocates (rename : Nat → Nat) (filters : List Expr) (body : List Stmt) :
    comprehensionFilters filters (body.map (relocateStmt rename)) =
      (comprehensionFilters filters body).map (relocateStmt rename) := by
  induction filters with
  | nil => rfl
  | cons head tail ih => simp [comprehensionFilters, relocateStmt, comprehensionFilters] at ih ⊢; exact ih

theorem comprehensionBody_relocates (rename : Nat → Nat) (address : Nat) (element : Expr)
    (generators : List (String × Expr × List Expr)) :
    comprehensionBody (rename address) element generators =
      (comprehensionBody address element generators).map (relocateStmt rename) := by
  induction generators with
  | nil => simp [comprehensionBody, relocateStmt]
  | cons generator rest ih =>
    rcases generator with ⟨name, iterable, filters⟩
    simp only [comprehensionBody, List.map_cons, List.map_nil, relocateStmt]
    rw [ih, comprehensionFilters_relocates]

theorem comprehensionTargetsBody_relocates (rename : Nat → Nat) (terminal : List Stmt)
    (generators : List (Expr × Expr × List Expr)) :
    comprehensionTargetsBody (terminal.map (relocateStmt rename)) generators =
      (comprehensionTargetsBody terminal generators).map (relocateStmt rename) := by
  induction generators with
  | nil => rfl
  | cons generator rest ih =>
    rcases generator with ⟨target, iterable, filters⟩
    simp only [comprehensionTargetsBody]
    split <;> simp only [List.map_cons, List.map_nil, relocateStmt, ih,
      comprehensionFilters_relocates, comprehensionTargetBody_relocates]

theorem comprehensionFilters_within (limit : Nat) (filters : List Expr) (body : List Stmt)
    (inside : ∀ statement ∈ body, StmtWithin limit statement) :
    ∀ statement ∈ comprehensionFilters filters body, StmtWithin limit statement := by
  induction filters with
  | nil => exact inside
  | cons head tail ih =>
    simpa only [comprehensionFilters, List.foldr_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, StmtWithin] using And.intro ih (by simp)

theorem comprehensionBody_within (limit address : Nat) (element : Expr)
    (generators : List (String × Expr × List Expr)) (inside : address < limit) :
    ∀ statement ∈ comprehensionBody address element generators, StmtWithin limit statement := by
  induction generators with
  | nil => simpa [comprehensionBody, StmtWithin] using inside
  | cons generator rest ih =>
    rcases generator with ⟨name, iterable, filters⟩
    simpa only [comprehensionBody, List.mem_cons, List.not_mem_nil, or_false, forall_eq, StmtWithin] using
      And.intro (comprehensionFilters_within limit filters _ ih) (by simp)

theorem comprehensionTargetsBody_within (limit : Nat) (terminal : List Stmt)
    (generators : List (Expr × Expr × List Expr))
    (inside : ∀ statement ∈ terminal, StmtWithin limit statement) :
    ∀ statement ∈ comprehensionTargetsBody terminal generators, StmtWithin limit statement := by
  induction generators with
  | nil => exact inside
  | cons generator rest ih =>
    rcases generator with ⟨target, iterable, filters⟩
    have filtered := comprehensionFilters_within limit filters _ ih
    have bound := comprehensionTargetBody_within limit target _ filtered
    simp only [comprehensionTargetsBody]
    split <;> simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, StmtWithin] <;>
      exact ⟨by assumption, by simp⟩

theorem comprehensionStart_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (target iterable : Expr) (body : List Stmt)
    (collector : Mutable.Object) (env : HeapCalls.Env) (address used anchors : Nat) (stack : List HeapCalls.Frame)
    (addressInside : address < logical.length) (envInside : EnvWithin logical.length env)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) :
    let nextMap := extendMap rename logical.length physical.length
    comprehensionStart target iterable (body.map (relocateStmt nextMap)) (relocateObject nextMap collector)
        (relocateEnv rename env) (rename address) (stack.map (relocateFrame rename)) physical used =
      relocateStep nextMap (physical ++ [relocateObject nextMap collector]) anchors
        (comprehensionStart target iterable body collector env address stack logical used) := by
  dsimp only
  have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem addressInside
  have moved := layout.lookup address _ found
  have agree := extendMap_old rename logical.length physical.length
  have envSame := relocateEnv_congr _ rename logical.length env agree envInside
  have stackSame := relocateStack_congr _ rename logical.length stack agree stackInside
  unfold comprehensionStart
  split <;> try rfl
  cases object : logical[address] <;>
    simp [object, relocateObject] at moved <;>
    simp [found, object, moved, relocateStep, Step.map, relocateCore, HeapCalls.Relocation.relocateState,
      relocateWork, relocateStmt, relocateFrame, comprehensionTargetBody_relocates,
      extendMap_new, agree address addressInside, envSame, stackSame]

theorem comprehensionStart_within (heap : Mutable.Heap) (target iterable : Expr) (body : List Stmt)
    (collector : Mutable.Object) (env : HeapCalls.Env) (address used : Nat) (stack : List HeapCalls.Frame)
    (addressInside : address < heap.length) (envInside : EnvWithin heap.length env)
    (bodyInside : ∀ statement ∈ body, StmtWithin (heap.length + 1) statement)
    (stackInside : ∀ frame ∈ stack, FrameWithin heap.length frame) :
    StepWithin (comprehensionStart target iterable body collector env address stack heap used) := by
  have bodyBound := comprehensionTargetBody_within (heap.length + 1) target body bodyInside
  unfold comprehensionStart
  split <;> try trivial
  cases found : heap[address]? with
  | none => trivial
  | some object =>
    cases object <;> try trivial
    simp only [StepWithin, HeapCalls.Relocation.StateWithin, WorkWithin, List.length_append, List.length_singleton]
    refine ⟨⟨envInside.mono (by omega), ?_⟩, ?_⟩
    · simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, StmtWithin] using
        And.intro (show address < heap.length + 1 by omega) (And.intro bodyBound (by simp))
    · intro frame member
      rcases List.mem_cons.mp member with rfl | member
      · simp [FrameWithin]
      · exact (stackInside frame member).mono (by omega)

theorem iterator_list_comprehension_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (choices : ChoiceSchedule) (name : String)
    (element iterable : Expr) (filters : List Expr) (generators : List (String × Expr × List Expr))
    (env : HeapCalls.Env) (address used logicalAnchors physicalAnchors : Nat) (stack : List HeapCalls.Frame)
    (globals : Mutable.Globals) (addressInside : address < logical.length) (envInside : EnvWithin logical.length env)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) :
    iteratorStep choices physicalAnchors
      (relocateCore rename physical ⟨⟨.operation (.comprehension element ((name, iterable, filters) :: generators) env) [.ref address], stack, logical⟩, used⟩)
      (relocateGlobals rename globals) =
      relocateStep (extendMap rename logical.length physical.length) (physical ++ [.list []]) physicalAnchors
        (iteratorStep choices logicalAnchors ⟨⟨.operation (.comprehension element ((name, iterable, filters) :: generators) env) [.ref address], stack, logical⟩, used⟩ globals) := by
  have paired := comprehensionStart_relocates layout (.name name) iterable
    (comprehensionFilters filters (comprehensionBody logical.length element generators)) (.list [])
    env address used physicalAnchors stack addressInside envInside stackInside
  simpa only [iteratorStep, relocateCore, HeapCalls.Relocation.relocateState, relocateWork,
    relocateRuntimeOperation, relocateOperation, List.map_cons, List.map_nil, relocateValue,
    ← comprehensionFilters_relocates, ← comprehensionBody_relocates, ← comprehensionTargetsBody_relocates,
    relocateStmt, extendMap_new, relocateObject] using paired

theorem iterator_targets_comprehension_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (choices : ChoiceSchedule) (target : Expr)
    (element iterable : Expr) (filters : List Expr) (generators : List (Expr × Expr × List Expr))
    (env : HeapCalls.Env) (address used logicalAnchors physicalAnchors : Nat) (stack : List HeapCalls.Frame)
    (globals : Mutable.Globals) (addressInside : address < logical.length) (envInside : EnvWithin logical.length env)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) :
    iteratorStep choices physicalAnchors
      (relocateCore rename physical ⟨⟨.operation (.comprehensionTargets element ((target, iterable, filters) :: generators) env) [.ref address], stack, logical⟩, used⟩)
      (relocateGlobals rename globals) =
      relocateStep (extendMap rename logical.length physical.length) (physical ++ [.list []]) physicalAnchors
        (iteratorStep choices logicalAnchors ⟨⟨.operation (.comprehensionTargets element ((target, iterable, filters) :: generators) env) [.ref address], stack, logical⟩, used⟩ globals) := by
  have paired := comprehensionStart_relocates layout target iterable
    (comprehensionFilters filters (comprehensionTargetsBody [.comprehensionAppend logical.length element] generators)) (.list [])
    env address used physicalAnchors stack addressInside envInside stackInside
  simpa only [iteratorStep, relocateCore, HeapCalls.Relocation.relocateState, relocateWork,
    relocateRuntimeOperation, relocateOperation, List.map_cons, List.map_nil, relocateValue,
    ← comprehensionFilters_relocates, ← comprehensionBody_relocates, ← comprehensionTargetsBody_relocates,
    relocateStmt, extendMap_new, relocateObject] using paired

theorem iterator_set_comprehension_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (choices : ChoiceSchedule) (target : Expr)
    (element iterable : Expr) (filters : List Expr) (generators : List (Expr × Expr × List Expr))
    (env : HeapCalls.Env) (address used logicalAnchors physicalAnchors : Nat) (stack : List HeapCalls.Frame)
    (globals : Mutable.Globals) (addressInside : address < logical.length) (envInside : EnvWithin logical.length env)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) :
    iteratorStep choices physicalAnchors
      (relocateCore rename physical ⟨⟨.operation (.setComprehension element ((target, iterable, filters) :: generators) env) [.ref address], stack, logical⟩, used⟩)
      (relocateGlobals rename globals) =
      relocateStep (extendMap rename logical.length physical.length) (physical ++ [.set []]) physicalAnchors
        (iteratorStep choices logicalAnchors ⟨⟨.operation (.setComprehension element ((target, iterable, filters) :: generators) env) [.ref address], stack, logical⟩, used⟩ globals) := by
  have paired := comprehensionStart_relocates layout target iterable
    (comprehensionFilters filters (comprehensionTargetsBody [.comprehensionAdd logical.length element] generators)) (.set [])
    env address used physicalAnchors stack addressInside envInside stackInside
  simpa only [iteratorStep, relocateCore, HeapCalls.Relocation.relocateState, relocateWork,
    relocateRuntimeOperation, relocateOperation, List.map_cons, List.map_nil, relocateValue,
    ← comprehensionFilters_relocates, ← comprehensionBody_relocates, ← comprehensionTargetsBody_relocates,
    relocateStmt, extendMap_new, relocateObject] using paired

theorem iterator_dict_comprehension_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (choices : ChoiceSchedule) (target key : Expr)
    (element iterable : Expr) (filters : List Expr) (generators : List (Expr × Expr × List Expr))
    (env : HeapCalls.Env) (address used logicalAnchors physicalAnchors : Nat) (stack : List HeapCalls.Frame)
    (globals : Mutable.Globals) (addressInside : address < logical.length) (envInside : EnvWithin logical.length env)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) :
    iteratorStep choices physicalAnchors
      (relocateCore rename physical ⟨⟨.operation (.dictionaryComprehension key element ((target, iterable, filters) :: generators) env) [.ref address], stack, logical⟩, used⟩)
      (relocateGlobals rename globals) =
      relocateStep (extendMap rename logical.length physical.length) (physical ++ [.dict []]) physicalAnchors
        (iteratorStep choices logicalAnchors ⟨⟨.operation (.dictionaryComprehension key element ((target, iterable, filters) :: generators) env) [.ref address], stack, logical⟩, used⟩ globals) := by
  have paired := comprehensionStart_relocates layout target iterable
    (comprehensionFilters filters (comprehensionTargetsBody [.comprehensionStore logical.length key element] generators)) (.dict [])
    env address used physicalAnchors stack addressInside envInside stackInside
  simpa only [iteratorStep, relocateCore, HeapCalls.Relocation.relocateState, relocateWork,
    relocateRuntimeOperation, relocateOperation, List.map_cons, List.map_nil, relocateValue,
    ← comprehensionFilters_relocates, ← comprehensionBody_relocates, ← comprehensionTargetsBody_relocates,
    relocateStmt, extendMap_new, relocateObject] using paired

theorem comprehensionEnv_relocates (rename : Nat → Nat) (env : HeapCalls.Env)
    (generators : List (String × Expr × List Expr)) :
    comprehensionEnv (relocateEnv rename env) generators = relocateEnv rename (comprehensionEnv env generators) := by
  funext name
  simp only [comprehensionEnv, relocateEnv]
  split <;> rfl

theorem comprehensionTargetsEnv_relocates (rename : Nat → Nat) (env : HeapCalls.Env)
    (generators : List (Expr × Expr × List Expr)) :
    comprehensionTargetsEnv (relocateEnv rename env) generators = relocateEnv rename (comprehensionTargetsEnv env generators) := by
  funext name
  simp only [comprehensionTargetsEnv, relocateEnv]
  split <;> rfl

theorem sumBody_source (element : Expr) (generators : List (String × Expr × List Expr)) :
    ∀ statement ∈ sumBody element generators, StmtWithin 0 statement := by
  induction generators with
  | nil => simp [sumBody, StmtWithin]
  | cons generator rest ih =>
    rcases generator with ⟨name, iterable, filters⟩
    simpa only [sumBody, List.mem_cons, List.not_mem_nil, or_false, forall_eq, StmtWithin] using
      And.intro (comprehensionFilters_within 0 filters _ ih) (by simp)

theorem extremumBody_source (maximum : Bool) (element : Expr) :
    ∀ statement ∈ extremumBody maximum element, StmtWithin 0 statement := by
  simp [extremumBody, StmtWithin]

theorem iterator_sum_generator_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (choices : ChoiceSchedule) (name : String)
    (element iterable start : Expr) (filters : List Expr) (generators : List (String × Expr × List Expr))
    (env : HeapCalls.Env) (address used logicalAnchors physicalAnchors : Nat) (stack : List HeapCalls.Frame)
    (globals : Mutable.Globals) (inside : address < logical.length) :
    iteratorStep choices physicalAnchors
      (relocateCore rename physical ⟨⟨.operation (.sumGenerator element ((name, iterable, filters) :: generators) env start)
        [.ref address], stack, logical⟩, used⟩) (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors (iteratorStep choices logicalAnchors
        ⟨⟨.operation (.sumGenerator element ((name, iterable, filters) :: generators) env start)
          [.ref address], stack, logical⟩, used⟩ globals) := by
  have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
  have moved := layout.lookup address _ found
  have bodySame := relocateBody_source rename _ (comprehensionFilters_within 0 filters _ (sumBody_source element generators))
  simp only [relocateCore, HeapCalls.Relocation.relocateState, relocateWork, relocateRuntimeOperation,
    relocateOperation, List.map_cons, List.map_nil, relocateValue, iteratorStep]
  split <;> try rfl
  cases object : logical[address] <;> simp only [object, relocateObject] at moved <;>
    simp [found, object, moved, relocateStep, Step.map, relocateCore, HeapCalls.Relocation.relocateState,
      relocateWork, relocateFrame, relocateStmt, comprehensionEnv_relocates, bodySame]

theorem iterator_extremum_generator_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (choices : ChoiceSchedule) (target : Expr)
    (maximum : Bool) (fallback : Option Expr) (element iterable : Expr) (filters : List Expr)
    (generators : List (Expr × Expr × List Expr)) (env : HeapCalls.Env)
    (address used logicalAnchors physicalAnchors : Nat) (stack : List HeapCalls.Frame)
    (globals : Mutable.Globals) (inside : address < logical.length) :
    iteratorStep choices physicalAnchors
      (relocateCore rename physical ⟨⟨.operation
        (.extremumGenerator maximum fallback element ((target, iterable, filters) :: generators) env)
        [.ref address], stack, logical⟩, used⟩) (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors (iteratorStep choices logicalAnchors
        ⟨⟨.operation (.extremumGenerator maximum fallback element ((target, iterable, filters) :: generators) env)
          [.ref address], stack, logical⟩, used⟩ globals) := by
  have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
  have moved := layout.lookup address _ found
  have bodySame := relocateBody_source rename _ (comprehensionTargetBody_within 0 target _
    (comprehensionFilters_within 0 filters _ (comprehensionTargetsBody_within 0 _ generators (extremumBody_source maximum element))))
  simp only [relocateCore, HeapCalls.Relocation.relocateState, relocateWork, relocateRuntimeOperation,
    relocateOperation, List.map_cons, List.map_nil, relocateValue, iteratorStep]
  split <;> try rfl
  cases object : logical[address] <;> simp only [object, relocateObject] at moved <;>
    simp [found, object, moved, relocateStep, Step.map, relocateCore, HeapCalls.Relocation.relocateState,
      relocateWork, relocateFrame, relocateStmt, comprehensionTargetsEnv_relocates, bodySame]

theorem sumInitial_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (value : Mutable.Value) (inside : value.edge.Within logical.length) :
    sumInitial (relocateValue rename value) physical =
      (sumInitial value logical).map (fun result => (result.1.map (relocateValue rename), physical)) := by
  cases value with
  | scalar value => cases value <;> simp [sumInitial, relocateValue, Mutable.error, Except.map]
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    cases object : logical[address] <;> simp only [object, relocateObject] at moved <;>
      simp [sumInitial, relocateValue, found, object, moved, Mutable.error, Except.map]

theorem sumInitial_keeps_heap (heap after : Mutable.Heap) (value : Mutable.Value)
    (outcome : Except ExceptionObject Mutable.Value) (inside : value.edge.Within heap.length)
    (executed : sumInitial value heap = some (outcome, after)) : after = heap := by
  have same := sumInitial_relocates (RuntimeLayout.refl heap) value inside
  simp only [relocateValue_id, executed, Option.map_some] at same
  exact congrArg Prod.snd (Option.some.inj same)

theorem sumEnter_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
    (loop : Stmt) (env : HeapCalls.Env) (value : Mutable.Value) (stack : List HeapCalls.Frame)
    (globals : Mutable.Globals) (inside : value.edge.Within logical.length) :
    sumEnter physicalAnchors (relocateStmt rename loop) (relocateEnv rename env) (relocateValue rename value)
        (stack.map (relocateFrame rename)) physical (relocateGlobals rename globals) =
      HeapCalls.Relocation.relocateStep rename physical physicalAnchors
        (sumEnter logicalAnchors loop env value stack logical globals) := by
  have paired := sumInitial_relocates layout value inside
  cases tested : sumInitial value logical with
  | none => simp [sumEnter, run, paired, tested, HeapCalls.Relocation.relocateStep]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have unchanged := sumInitial_keeps_heap logical after value outcome inside tested
    subst after
    cases outcome <;>
      simp [sumEnter, run, paired, tested, HeapCalls.Relocation.relocateStep, relocateCompletion, Except.map,
        HeapCalls.Relocation.relocateState, relocateWork, relocateStmt, relocateEnv_set, done]

theorem iterator_sum_sequence_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (choices : ChoiceSchedule)
    (address used logicalAnchors physicalAnchors : Nat) (value : Mutable.Value) (stack : List HeapCalls.Frame)
    (globals : Mutable.Globals) (addressInside : address < logical.length) (valueInside : value.edge.Within logical.length) :
    iteratorStep choices physicalAnchors
      (relocateCore rename physical ⟨⟨.operation .sumSequence [.ref address, value], stack, logical⟩, used⟩)
      (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors (iteratorStep choices logicalAnchors
        ⟨⟨.operation .sumSequence [.ref address, value], stack, logical⟩, used⟩ globals) := by
  have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem addressInside
  have moved := layout.lookup address _ found
  cases object : logical[address] with
  | set items =>
    simp only [object, relocateObject] at moved
    have paired := sumEnter_relocates layout logicalAnchors physicalAnchors
      (.setStepLoop sumItem address items items (sumBody (.name sumItem) []) []) (fun _ => none) value stack globals valueInside
    simp only [relocateCore, HeapCalls.Relocation.relocateState, relocateWork, relocateRuntimeOperation, relocateOperation,
      List.map_cons, List.map_nil, relocateValue, iteratorStep, found, object, moved]
    have lifted := congrArg (liftStep used) paired
    rw [IteratorCalls.Relocation.set_lift_relocates] at lifted
    simpa [relocateStep, relocateStmt, sumBody, relocateEnv] using lifted
  | _ =>
    simp only [object, relocateObject] at moved
    simp [relocateCore, HeapCalls.Relocation.relocateState, relocateWork, relocateRuntimeOperation, relocateOperation,
      relocateValue, iteratorStep, found, object, moved, relocateStep, Step.map]

/-- Every set fallback branch has a matching step, including unsupported states.
Allocation may extend the map; saved old references keep their addresses. -/
theorem iteratorStep_relocates (choices : ChoiceSchedule) (core : SetCalls.State)
    (physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (globals : Mutable.Globals) (layout : RuntimeLayout core.core.heap physical rename)
    (inside : HeapCalls.Relocation.StateWithin core.core) :
    ∃ physicalAfter nextMap,
      (∀ address < core.core.heap.length, nextMap address = rename address) ∧
      iteratorStep choices physicalAnchors (relocateCore rename physical core) (relocateGlobals rename globals) =
        relocateStep nextMap physicalAfter physicalAnchors (iteratorStep choices logicalAnchors core globals) := by
  rcases core with ⟨⟨work, stack, logical⟩, used⟩
  have unchanged (paired : iteratorStep choices physicalAnchors
      (relocateCore rename physical ⟨⟨work, stack, logical⟩, used⟩) (relocateGlobals rename globals) =
        relocateStep rename physical physicalAnchors (iteratorStep choices logicalAnchors ⟨⟨work, stack, logical⟩, used⟩ globals)) :
      ∃ physicalAfter nextMap,
        (∀ address < logical.length, nextMap address = rename address) ∧
        iteratorStep choices physicalAnchors (relocateCore rename physical ⟨⟨work, stack, logical⟩, used⟩)
          (relocateGlobals rename globals) =
          relocateStep nextMap physicalAfter physicalAnchors (iteratorStep choices logicalAnchors ⟨⟨work, stack, logical⟩, used⟩ globals) :=
    ⟨physical, rename, fun _ _ => rfl, paired⟩
  cases work with
  | value value =>
    apply unchanged
    cases value with
    | scalar value => rfl
    | ref address =>
      cases stack with
      | nil => rfl
      | cons frame stack =>
        cases frame with
        | sequence name body otherwise following env =>
          exact iterator_sequence_relocates layout choices logicalAnchors physicalAnchors used address name
            body otherwise following env stack globals inside.1
        | _ => simp [relocateCore, HeapCalls.Relocation.relocateState, relocateWork, relocateValue,
            relocateFrame, iteratorStep, relocateStep, Step.map]
  | block statements env =>
    apply unchanged
    cases statements with
    | nil => rfl
    | cons statement following =>
      cases statement with
      | setStepLoop name address original remaining body otherwise =>
        have cursorInside := inside.1.2 _ (List.mem_cons_self ..)
        simp only [StmtWithin] at cursorInside
        exact iterator_cursor_relocates layout choices logicalAnchors physicalAnchors used address name
          original remaining body otherwise following env stack globals cursorInside.1
      | _ => simp [relocateCore, HeapCalls.Relocation.relocateState, relocateWork, relocateStmt,
          iteratorStep, relocateStep, Step.map]
  | operation operation values =>
    cases operation with
    | comprehension element generators env | comprehensionTargets element generators env
    | setComprehension element generators env | dictionaryComprehension key element generators env
    | sumGenerator element generators env start | extremumGenerator maximum fallback element generators env =>
      cases generators with
      | nil => exact unchanged rfl
      | cons generator generators =>
        rcases generator with ⟨target, iterable, filters⟩
        cases values with
        | nil => exact unchanged rfl
        | cons value values =>
          cases values with
          | cons =>
            apply unchanged
            cases value <;> rfl
          | nil =>
            cases value with
            | scalar value => exact unchanged rfl
            | ref address =>
              have addressInside := inside.1.2 (.ref address) (List.mem_cons_self ..)
              first
                | exact ⟨physical ++ [.list []], extendMap rename logical.length physical.length,
                    extendMap_old rename logical.length physical.length,
                    iterator_list_comprehension_relocates layout choices target element iterable filters generators env
                      address used logicalAnchors physicalAnchors stack globals addressInside inside.1.1 inside.2⟩
                | exact ⟨physical ++ [.list []], extendMap rename logical.length physical.length,
                    extendMap_old rename logical.length physical.length,
                    iterator_targets_comprehension_relocates layout choices target element iterable filters generators env
                      address used logicalAnchors physicalAnchors stack globals addressInside inside.1.1 inside.2⟩
                | exact ⟨physical ++ [.set []], extendMap rename logical.length physical.length,
                    extendMap_old rename logical.length physical.length,
                    iterator_set_comprehension_relocates layout choices target element iterable filters generators env
                      address used logicalAnchors physicalAnchors stack globals addressInside inside.1.1 inside.2⟩
                | exact ⟨physical ++ [.dict []], extendMap rename logical.length physical.length,
                    extendMap_old rename logical.length physical.length,
                    iterator_dict_comprehension_relocates layout choices target key element iterable filters generators env
                      address used logicalAnchors physicalAnchors stack globals addressInside inside.1.1 inside.2⟩
                | exact unchanged (iterator_sum_generator_relocates layout choices target element iterable start filters generators env
                    address used logicalAnchors physicalAnchors stack globals addressInside)
                | exact unchanged (iterator_extremum_generator_relocates layout choices target maximum fallback element iterable filters generators env
                    address used logicalAnchors physicalAnchors stack globals addressInside)
    | sumSequence =>
      apply unchanged
      cases values with
      | nil => rfl
      | cons value values =>
        cases value with
        | scalar value => rfl
        | ref address =>
          cases values with
          | nil => rfl
          | cons start values =>
            cases values with
            | cons => rfl
            | nil =>
              exact iterator_sum_sequence_relocates layout choices address used logicalAnchors physicalAnchors start stack globals
                (inside.1.2 (.ref address) (by simp)) (inside.1.2 start (by simp))
    | _ =>
      apply unchanged
      simp [relocateCore, HeapCalls.Relocation.relocateState, relocateWork, relocateRuntimeOperation,
        relocateOperation, iteratorStep, relocateStep, Step.map]
  | _ =>
    apply unchanged
    simp [relocateCore, HeapCalls.Relocation.relocateState, relocateWork, iteratorStep, relocateStep, Step.map]

end FormalSW.PyAst.SetCalls.Relocation
