import lang.py.FormalSW.IteratorRelocation
import lang.py.FormalSW.ExecutionSimulation

/-! Implicit iterator method entry preserves source code and saved consumers. -/
namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation
set_option Elab.async false

/-- Parsed module definitions contain no live heap addresses. -/
def ModuleSource (module : Module) : Prop := ∀ statement ∈ module.body, StmtWithin 0 statement

theorem findFunctionIn_within (limit : Nat) (statements : List Stmt) (name : String)
    (args : List Arg) (body : List Stmt)
    (inside : ∀ statement ∈ statements, StmtWithin limit statement)
    (found : findFunctionIn statements name = some (args, body)) :
    ∀ statement ∈ body, StmtWithin limit statement := by
  induction statements with
  | nil => simp [findFunctionIn] at found
  | cons head tail ih =>
    have first := inside head (by simp)
    have rest := ih (fun statement member => inside statement (List.mem_cons_of_mem _ member))
    cases head <;> simp only [findFunctionIn] at found
    all_goals first
      | exact rest found
      | split at found
        · cases found; simpa only [StmtWithin] using first
        · exact rest found

theorem findClassBodyIn_within (limit : Nat) (statements : List Stmt) (name : String)
    (body : List Stmt) (inside : ∀ statement ∈ statements, StmtWithin limit statement)
    (found : findClassBodyIn statements name = some body) :
    ∀ statement ∈ body, StmtWithin limit statement := by
  induction statements with
  | nil => simp [findClassBodyIn] at found
  | cons head tail ih =>
    have first := inside head (by simp)
    have rest := ih (fun statement member => inside statement (List.mem_cons_of_mem _ member))
    cases head <;> simp only [findClassBodyIn] at found
    all_goals first
      | exact rest found
      | split at found
        · cases found; simpa only [StmtWithin] using first
        · exact rest found

theorem findClass_within (module : Module) (name origin : String) (body : List Stmt)
    (source : ModuleSource module) (found : module.findClass name = some (origin, body)) :
    ∀ statement ∈ body, StmtWithin 0 statement := by
  unfold Module.findClass at found
  cases located : module.classOrigins.lookup name <;> simp [located] at found
  case some identity =>
    cases defined : module.findClassBody name <;> simp [defined] at found
    case some code =>
      rcases found with ⟨rfl, rfl⟩
      exact findClassBodyIn_within 0 module.body name code source defined

/-- Lookup can only bind a method from the module's source declarations. -/
def SourceMethod (receiver : Mutable.Value) (operation : Operation) : Prop :=
  ∃ args body, operation = .method receiver args body ∧ ∀ statement ∈ body, StmtWithin 0 statement

theorem lookup_source (module : Module) (receiver : Mutable.Value) (name : String)
    (heap after : Mutable.Heap) (operation : Operation) (source : ModuleSource module)
    (found : ProtocolCalls.lookup module receiver name heap = some (.ok (some operation), after)) :
    SourceMethod receiver operation := by
  cases receiver with
  | scalar value => simp [ProtocolCalls.lookup, Mutable.unsupported] at found
  | ref address =>
    cases cell : heap[address]? with
    | none => simp [ProtocolCalls.lookup, cell, Mutable.unsupported] at found
    | some object =>
      cases object with
      | «instance» origin className fields | dataInstance origin className frozen declared fields =>
        cases definition : module.findClass className with
        | none => simp [ProtocolCalls.lookup, cell, instanceClass, definition, Mutable.unsupported] at found
        | some pair =>
          rcases pair with ⟨identity, code⟩
          by_cases nominal : identity = origin
          · cases method : findFunctionIn code name with
            | none => simp [ProtocolCalls.lookup, cell, instanceClass, definition, nominal, method, Except.map] at found
            | some pair =>
              rcases pair with ⟨args, body⟩
              simp [ProtocolCalls.lookup, cell, instanceClass, definition, nominal, method, Except.map] at found
              exact ⟨args, body, found.1.symm,
                findFunctionIn_within 0 code name args body (findClass_within module className identity code source definition) method⟩
          · simp [ProtocolCalls.lookup, cell, instanceClass, definition, nominal, Mutable.unsupported] at found
      | _ => simp [ProtocolCalls.lookup, cell, Mutable.unsupported] at found

theorem SourceMethod.relocate (rename : Nat → Nat) {receiver : Mutable.Value} {operation : Operation}
    (source : SourceMethod receiver operation) :
    relocateRuntimeOperation rename operation = relocateOperation rename operation := by
  rcases source with ⟨args, body, rfl, code⟩
  simp only [relocateRuntimeOperation, relocateOperation, relocateBody_source rename body code]

theorem nextMethod_source (module : Module) (receiver : Mutable.Value)
    (heap after : Mutable.Heap) (operation : Operation) (source : ModuleSource module)
    (found : ProtocolCalls.nextMethod module receiver heap = some (.ok (some operation), after)) :
    SourceMethod receiver operation := by
  cases receiver with
  | scalar value => simp [ProtocolCalls.nextMethod] at found
  | ref address =>
    cases cell : heap[address]? with
    | none => simp [ProtocolCalls.nextMethod, cell, Mutable.unsupported] at found
    | some object =>
      cases object with
      | «instance» origin className fields | dataInstance origin className frozen declared fields =>
        apply lookup_source module (.ref address) "__next__" heap after operation source
        simpa [ProtocolCalls.nextMethod, cell] using found
      | _ => simp [ProtocolCalls.nextMethod, cell] at found

theorem iterMethod_source (module : Module) (receiver : Mutable.Value)
    (heap after : Mutable.Heap) (operation : Operation) (source : ModuleSource module)
    (found : ProtocolCalls.iterMethod module receiver heap = some (.ok operation, after)) :
    SourceMethod receiver operation := by
  cases searched : ProtocolCalls.lookup module receiver "__iter__" heap with
  | none => simp [ProtocolCalls.iterMethod, Mutable.eval_bind, searched] at found
  | some pair =>
    rcases pair with ⟨outcome, middle⟩
    cases outcome with
    | error error => simp [ProtocolCalls.iterMethod, Mutable.eval_bind, searched] at found
    | ok method =>
      cases method with
      | some bound =>
        simp [ProtocolCalls.iterMethod, Mutable.eval_bind, searched] at found
        obtain ⟨rfl, rfl⟩ := found
        exact lookup_source module receiver "__iter__" heap middle bound source searched
      | none =>
        cases checked : ProtocolCalls.lookup module receiver "__getitem__" middle with
        | none => simp [ProtocolCalls.iterMethod, Mutable.eval_bind, searched, checked] at found
        | some pair =>
          rcases pair with ⟨outcome, finalHeap⟩
          cases outcome with
          | error error => simp [ProtocolCalls.iterMethod, Mutable.eval_bind, searched, checked] at found
          | ok fallback =>
            cases fallback <;>
              simp [ProtocolCalls.iterMethod, Mutable.eval_bind, searched, checked, Mutable.error, Mutable.unsupported] at found

theorem nextMethod_runtime_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (module : Module) (receiver : Mutable.Value)
    (source : ModuleSource module) (inside : receiver.edge.Within logical.length) :
    ProtocolCalls.nextMethod module (relocateValue rename receiver) physical =
      (ProtocolCalls.nextMethod module receiver logical).map
        (fun result => (result.1.map (Option.map (relocateRuntimeOperation rename)), physical)) := by
  have paired := nextMethod_relocates layout module receiver inside
  cases tested : ProtocolCalls.nextMethod module receiver logical with
  | none => simpa only [tested] using paired
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    cases outcome with
    | error error => simpa only [tested, Option.map_some, Except.map] using paired
    | ok method =>
      cases method with
      | none => simpa only [tested, Option.map_some, Except.map, Option.map_none] using paired
      | some operation =>
        have same := (nextMethod_source module receiver logical after operation source tested).relocate rename
        simpa only [tested, Option.map_some, Except.map, same] using paired

theorem iterMethod_runtime_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (module : Module) (receiver : Mutable.Value)
    (source : ModuleSource module) (inside : receiver.edge.Within logical.length) :
    ProtocolCalls.iterMethod module (relocateValue rename receiver) physical =
      (ProtocolCalls.iterMethod module receiver logical).map
        (fun result => (result.1.map (relocateRuntimeOperation rename), physical)) := by
  have paired := iterMethod_relocates layout module receiver inside
  cases tested : ProtocolCalls.iterMethod module receiver logical with
  | none => simpa only [tested] using paired
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    cases outcome with
    | error error => simpa only [tested, Option.map_some, Except.map] using paired
    | ok operation =>
      have same := (iterMethod_source module receiver logical after operation source tested).relocate rename
      simpa only [tested, Option.map_some, Except.map, same] using paired

theorem enter_relocates (rename : Nat → Nat) (logical physical : Mutable.Heap)
    (logicalAnchors physicalAnchors used : Nat) (resumes : List Resume) (pending : Resume)
    (method moved : Mutable.Eval Operation) (globals : Mutable.Globals)
    (paired : moved physical = (method logical).map
      (fun result => (result.1.map (relocateRuntimeOperation rename), physical))) :
    enter physicalAnchors physical used (resumes.map (relocateResume rename))
        (relocateResume rename pending) moved (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (enter logicalAnchors logical used resumes pending method globals) := by
  simp only [enter, paired]
  cases tested : method logical with
  | none => rfl
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    cases outcome <;> rfl

/-- The next slot must exist before its method can be entered. -/
def advanceMethod (module : Module) (iterator : Mutable.Value) : Mutable.Eval Operation := do
  match ← ProtocolCalls.nextMethod module iterator with
  | some operation => pure operation
  | none => Mutable.error "TypeError"

theorem advanceMethod_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (module : Module) (iterator : Mutable.Value)
    (source : ModuleSource module) (inside : iterator.edge.Within logical.length) :
    advanceMethod module (relocateValue rename iterator) physical =
      (advanceMethod module iterator logical).map
        (fun result => (result.1.map (relocateRuntimeOperation rename), physical)) := by
  have paired := nextMethod_runtime_relocates layout module iterator source inside
  cases tested : ProtocolCalls.nextMethod module iterator logical with
  | none => simp [advanceMethod, Mutable.eval_bind, paired, tested]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    cases outcome with
    | error error => simp [advanceMethod, Mutable.eval_bind, paired, tested, Except.map]
    | ok method => cases method <;> simp [advanceMethod, Mutable.eval_bind, paired, tested, Except.map, Mutable.error]

theorem intercept_acquire_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (module : Module) (receiver : Mutable.Value)
    (logicalAnchors physicalAnchors used : Nat) (loop : Loop) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module) (inside : receiver.edge.Within logical.length) :
    intercept module physicalAnchors
      (relocateCore rename physical ⟨⟨.value receiver,
        .sequence loop.name loop.body loop.otherwise loop.following loop.env :: loop.stack, logical⟩, used⟩)
      (resumes.map (relocateResume rename)) (relocateGlobals rename globals) =
      (intercept module logicalAnchors ⟨⟨.value receiver,
        .sequence loop.name loop.body loop.otherwise loop.following loop.env :: loop.stack, logical⟩, used⟩
        resumes globals).map (relocateStep rename physical physicalAnchors) := by
  have paired := enter_relocates rename logical physical logicalAnchors physicalAnchors used resumes
    (.acquire loop) _ _ globals (iterMethod_runtime_relocates layout module receiver source inside)
  simp only [relocateCore, HeapCalls.Relocation.relocateState, relocateWork, List.map_cons, relocateFrame,
    intercept, isInstance_relocates layout receiver inside]
  by_cases instanceFound : isInstance logical receiver
  · simpa only [instanceFound, if_true, Option.map_some, relocateResume, relocateLoop] using congrArg some paired
  · simp [instanceFound]

theorem intercept_advance_relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (module : Module) (cursor : SequenceSource) (index : Nat)
    (logicalAnchors physicalAnchors used : Nat) (loop : Loop) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module) (inside : SourceWithin logical.length cursor) :
    intercept module physicalAnchors
      (relocateCore rename physical ⟨⟨.block
        (.sequenceStepLoop loop.name cursor index loop.body loop.otherwise :: loop.following) loop.env,
        loop.stack, logical⟩, used⟩)
      (resumes.map (relocateResume rename)) (relocateGlobals rename globals) =
      (intercept module logicalAnchors ⟨⟨.block
        (.sequenceStepLoop loop.name cursor index loop.body loop.otherwise :: loop.following) loop.env,
        loop.stack, logical⟩, used⟩ resumes globals).map (relocateStep rename physical physicalAnchors) := by
  have paired := enter_relocates rename logical physical logicalAnchors physicalAnchors used resumes
    (.advance loop (sequenceValue cursor)) _ _ globals
    (advanceMethod_relocates layout module (sequenceValue cursor) source inside.value)
  simp only [relocateCore, HeapCalls.Relocation.relocateState, relocateWork, List.map_cons, relocateStmt,
    intercept, sequenceValue_relocate, isInstance_relocates layout (sequenceValue cursor) inside.value]
  by_cases instanceFound : isInstance logical (sequenceValue cursor)
  · simpa only [instanceFound, if_true, Option.map_some, relocateResume, relocateLoop, advanceMethod] using congrArg some paired
  · simp [instanceFound]

theorem intercept_relocates (module : Module) (core : SetCalls.State) (physical : Mutable.Heap)
    (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module)
    (layout : RuntimeLayout core.core.heap physical rename)
    (workInside : WorkWithin core.core.heap.length core.core.work) :
    intercept module physicalAnchors (relocateCore rename physical core)
        (resumes.map (relocateResume rename)) (relocateGlobals rename globals) =
      (intercept module logicalAnchors core resumes globals).map (relocateStep rename physical physicalAnchors) := by
  rcases core with ⟨⟨work, stack, logical⟩, used⟩
  cases work with
  | value receiver =>
    cases stack with
    | nil => rfl
    | cons frame stack =>
      cases frame with
      | sequence name body otherwise following env =>
        exact intercept_acquire_relocates layout module receiver logicalAnchors physicalAnchors used
          ⟨name, body, otherwise, following, env, stack⟩ resumes globals source workInside
      | _ => simp [relocateCore, HeapCalls.Relocation.relocateState, relocateWork, relocateFrame, intercept]
  | block statements env =>
    cases statements with
    | nil => rfl
    | cons statement following =>
      cases statement with
      | sequenceStepLoop name cursor index body otherwise =>
        have bounded := workInside.2 _ (List.mem_cons_self ..)
        simp only [StmtWithin] at bounded
        exact intercept_advance_relocates layout module cursor index logicalAnchors physicalAnchors used
          ⟨name, body, otherwise, following, env, stack⟩ resumes globals source bounded.1
      | _ => simp [relocateCore, HeapCalls.Relocation.relocateState, relocateWork, relocateStmt, intercept]
  | _ => simp [relocateCore, HeapCalls.Relocation.relocateState, relocateWork, intercept]

/-- Core execution and protocol dispatch compose without assuming that interception succeeds. -/
theorem lift_relocates (rename : Nat → Nat) (physical : Mutable.Heap) (anchors used : Nat)
    (resumes : List Resume) (transition : Step SetCalls.State Mutable.Completion) :
    lift used (resumes.map (relocateResume rename))
      (transition.map (relocateCore rename physical) (relocateCompletion rename physical anchors)) =
      relocateStep rename physical anchors (lift used resumes transition) := by
  cases transition <;> rfl

theorem SourceMethod.within (limit : Nat) {receiver : Mutable.Value} {operation : Operation}
    (source : SourceMethod receiver operation) (inside : receiver.edge.Within limit) :
    OperationWithin limit operation := by
  rcases source with ⟨args, body, rfl, code⟩
  simp only [OperationWithin]
  exact ⟨inside, fun statement member => (code statement member).mono (Nat.zero_le limit)⟩

theorem advanceMethod_source (module : Module) (receiver : Mutable.Value)
    (heap after : Mutable.Heap) (operation : Operation) (source : ModuleSource module)
    (found : advanceMethod module receiver heap = some (.ok operation, after)) :
    SourceMethod receiver operation := by
  cases tested : ProtocolCalls.nextMethod module receiver heap with
  | none => simp [advanceMethod, Mutable.eval_bind, tested] at found
  | some pair =>
    rcases pair with ⟨outcome, middle⟩
    cases outcome with
    | error error => simp [advanceMethod, Mutable.eval_bind, tested] at found
    | ok method =>
      cases method with
      | none => simp [advanceMethod, Mutable.eval_bind, tested, Mutable.error] at found
      | some bound =>
        simp [advanceMethod, Mutable.eval_bind, tested] at found
        obtain ⟨rfl, rfl⟩ := found
        exact nextMethod_source module receiver heap middle bound source tested

theorem enter_within (limit anchors used : Nat) (heap : Mutable.Heap) (resumes : List Resume)
    (pending : Resume) (method : Mutable.Eval Operation) (globals : Mutable.Globals)
    (saved : ResumeWithin limit pending) (rest : ∀ pending ∈ resumes, ResumeWithin limit pending)
    (globalsInside : GlobalsWithin limit globals)
    (methodInside : ∀ operation after, method heap = some (.ok operation, after) → OperationWithin limit operation) :
    StepWithin limit (enter anchors heap used resumes pending method globals) := by
  have allSaved : ∀ item ∈ pending :: resumes, ResumeWithin limit item := by
    intro item member
    rcases List.mem_cons.mp member with rfl | member
    · exact saved
    · exact rest item member
  cases tested : method heap with
  | none => simp [enter, tested, StepWithin]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    cases outcome with
    | error error =>
      simp only [enter, tested, StepWithin, StateWithin]
      exact ⟨globalsInside, (by intro _ impossible; cases impossible), allSaved⟩
    | ok operation =>
      simp only [enter, tested, StepWithin, StateWithin, WorkWithin]
      exact ⟨⟨methodInside operation after tested, by simp⟩, by simp, allSaved⟩

theorem intercept_within (module : Module) (core : SetCalls.State) (anchors : Nat)
    (resumes : List Resume) (globals : Mutable.Globals) (transition : Step State Mutable.Completion)
    (source : ModuleSource module) (inside : StateWithin core.core.heap.length (.running core resumes))
    (globalsInside : GlobalsWithin core.core.heap.length globals)
    (intercepted : intercept module anchors core resumes globals = some transition) :
    StepWithin core.core.heap.length transition := by
  rcases core with ⟨⟨work, stack, heap⟩, used⟩
  cases work with
  | value receiver =>
    cases stack with
    | nil => simp [intercept] at intercepted
    | cons frame stack =>
      cases frame with
      | sequence name body otherwise following env =>
        have frameInside := inside.2.1 _ (List.mem_cons_self ..)
        simp only [FrameWithin] at frameInside
        have loopInside : LoopWithin heap.length ⟨name, body, otherwise, following, env, stack⟩ :=
          ⟨frameInside.1, frameInside.2.1, frameInside.2.2.1, frameInside.2.2.2,
            fun frame member => inside.2.1 frame (List.mem_cons_of_mem _ member)⟩
        simp only [intercept] at intercepted
        split at intercepted
        · cases intercepted
          exact enter_within heap.length anchors used heap resumes _ _ globals loopInside inside.2.2 globalsInside
            (fun operation after found => (iterMethod_source module receiver heap after operation source found).within heap.length inside.1)
        · cases intercepted
      | _ => simp [intercept] at intercepted
  | block statements env =>
    cases statements with
    | nil => simp [intercept] at intercepted
    | cons statement following =>
      cases statement with
      | sequenceStepLoop name cursor index body otherwise =>
        have statementInside := inside.1.2 _ (List.mem_cons_self ..)
        simp only [StmtWithin] at statementInside
        have loopInside : LoopWithin heap.length ⟨name, body, otherwise, following, env, stack⟩ :=
          ⟨inside.1.1, statementInside.2.1, statementInside.2.2,
            fun statement member => inside.1.2 statement (List.mem_cons_of_mem _ member), inside.2.1⟩
        simp only [intercept] at intercepted
        split at intercepted
        · cases intercepted
          exact enter_within heap.length anchors used heap resumes _ (advanceMethod module (sequenceValue cursor)) globals
            ⟨loopInside, statementInside.1.value⟩ inside.2.2 globalsInside
            (fun operation after found => (advanceMethod_source module (sequenceValue cursor) heap after operation source found).within heap.length statementInside.1.value)
        · cases intercepted
      | _ => simp [intercept] at intercepted
  | _ => simp [intercept] at intercepted

theorem step_intercepted_relocates (module : Module) (core : SetCalls.State) (physical : Mutable.Heap)
    (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat) (choices : ChoiceSchedule)
    (resumes : List Resume) (globals : Mutable.Globals) (transition : Step State Mutable.Completion)
    (source : ModuleSource module) (layout : RuntimeLayout core.core.heap physical rename)
    (workInside : WorkWithin core.core.heap.length core.core.work)
    (intercepted : intercept module logicalAnchors core resumes globals = some transition) :
    IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.running core resumes)) (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (IteratorCalls.step module logicalAnchors choices (.running core resumes) globals) := by
  have paired := intercept_relocates module core physical rename logicalAnchors physicalAnchors resumes globals source layout workInside
  simp only [relocateState, IteratorCalls.step, paired, intercepted, Option.map_some]

end FormalSW.PyAst.IteratorCalls.Relocation
