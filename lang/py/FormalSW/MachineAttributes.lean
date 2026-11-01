import lang.py.FormalSW.AttributeRelocation

/-! Attribute dispatch retains the receiver while evaluating arguments and augmented assignments. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem bindMethod_reverse (module : Module) (receiver : Value) :
    bindMethod module receiver "$formalsw.sort.reverse" = (do
      let operation ← bindMethod module receiver "sort"
      match operation with
      | .sort address => pure (.sortReverse address)
      | _ => Mutable.unsupported) := by
  rfl

theorem bindMethod_relocates (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : RuntimeLayout logical physical rename) (module : Module) (receiver : Value) (name : String)
    (inside : receiver.edge.Within logical.length) :
    bindMethod module (relocateValue rename receiver) name physical =
      (bindMethod module receiver name logical).map
        (fun result => (result.1.map (relocateOperation rename), physical)) := by
  by_cases reverse : name = "$formalsw.sort.reverse"
  · subst name
    have paired := bindMethod_ordinary_relocates logical physical rename layout module receiver "sort" inside (by decide)
    rw [bindMethod_reverse, bindMethod_reverse]
    cases executed : bindMethod module receiver "sort" logical with
    | none => simp [Mutable.eval_bind, executed, paired]
    | some pair =>
      rcases pair with ⟨outcome, after⟩
      have stationary := bindMethod_ordinary_relocates logical logical id (RuntimeLayout.refl logical)
        module receiver "sort" inside (by decide)
      simp only [relocateValue_id, executed, Option.map_some] at stationary
      have same : after = logical := congrArg Prod.snd (Option.some.inj stationary)
      subst after
      cases outcome with
      | error exception => simp [Mutable.eval_bind, executed, paired, Except.map]
      | ok operation =>
        cases operation <;> simp [Mutable.eval_bind, executed, paired, Except.map,
          relocateOperation, Mutable.unsupported]
  · exact bindMethod_ordinary_relocates logical physical rename layout module receiver name inside reverse

theorem bindMethod_keeps_heap (module : Module) (receiver : Value) (name : String)
    (heap after : Mutable.Heap) (outcome : Except ExceptionObject Operation)
    (inside : receiver.edge.Within heap.length)
    (executed : bindMethod module receiver name heap = some (outcome, after)) : after = heap := by
  have stationary := bindMethod_relocates heap heap id (RuntimeLayout.refl heap) module receiver name inside
  simp only [relocateValue_id, executed, Option.map_some] at stationary
  exact congrArg Prod.snd (Option.some.inj stationary)

/-- Address-free source bodies remain address-free when selected as methods. -/
theorem findFunctionIn_within (limit : Nat) (statements : List Stmt) (name : String)
    (args : List Arg) (body : List Stmt)
    (source : ∀ statement ∈ statements, StmtWithin limit statement)
    (found : findFunctionIn statements name = some (args, body)) :
    ∀ statement ∈ body, StmtWithin limit statement := by
  induction statements with
  | nil => simp [findFunctionIn] at found
  | cons first rest ih =>
    have head := source first (by simp)
    have tail : ∀ statement ∈ rest, StmtWithin limit statement := fun statement member => source statement (by simp [member])
    cases first with
    | functionDef other parameters annotation methodBody =>
      by_cases same : name = other
      · have selected : parameters = args ∧ methodBody = body := by simpa [findFunctionIn, same] using found
        simpa only [StmtWithin, selected.2] using head
      · exact ih tail (by simpa only [findFunctionIn, if_neg same] using found)
    | _ => exact ih tail found

theorem findClassBodyIn_within (limit : Nat) (statements : List Stmt) (name : String) (body : List Stmt)
    (source : ∀ statement ∈ statements, StmtWithin limit statement)
    (found : findClassBodyIn statements name = some body) :
    ∀ statement ∈ body, StmtWithin limit statement := by
  induction statements with
  | nil => simp [findClassBodyIn] at found
  | cons first rest ih =>
    have head := source first (by simp)
    have tail : ∀ statement ∈ rest, StmtWithin limit statement := fun statement member => source statement (by simp [member])
    cases first with
    | classDef other classBody =>
      by_cases same : other = name
      · have selected : classBody = body := by simpa [findClassBodyIn, same] using found
        simpa only [StmtWithin, selected] using head
      · exact ih tail (by simpa only [findClassBodyIn, if_neg same] using found)
    | _ => exact ih tail found

theorem findClass_within (limit : Nat) (module : Module) (name origin : String) (body : List Stmt)
    (source : ∀ statement ∈ module.body, StmtWithin limit statement)
    (found : module.findClass name = some (origin, body)) :
    ∀ statement ∈ body, StmtWithin limit statement := by
  cases originFound : module.classOrigins.lookup name with
  | none => simp [Module.findClass, originFound] at found
  | some identity =>
    cases selected : findClassBodyIn module.body name with
    | none => simp [Module.findClass, Module.findClassBody, originFound, selected] at found
    | some classBody =>
      have same : identity = origin ∧ classBody = body := by
        simpa [Module.findClass, Module.findClassBody, originFound, selected] using found
      exact findClassBodyIn_within limit module.body name body source (same.2 ▸ selected)

/-- The callback condition relates source method bodies to their runtime representation. -/
theorem step_methodReceiver_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
    (receiver : Value) (name : String) (expressions : List Expr) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals)
    (receiverInside : receiver.edge.Within logical.length)
    (envInside : EnvWithin logical.length env)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals)
    (outcome : Except ExceptionObject Operation) (after : Mutable.Heap)
    (executed : bindMethod module receiver name logical = some (outcome, after))
    (operationInside : ∀ operation, outcome = .ok operation → OperationWithin logical.length operation)
    (source : ∀ operation, outcome = .ok operation →
      relocateRuntimeOperation rename operation = relocateOperation rename operation) :
    after = logical ∧
      step module physicalAnchors
          (relocateState rename physical ⟨.value receiver, .methodReceiver name expressions env :: stack, logical⟩)
          (relocateGlobals rename globals) =
        relocateStep rename physical physicalAnchors
          (step module logicalAnchors ⟨.value receiver, .methodReceiver name expressions env :: stack, logical⟩ globals) ∧
      StepWithin (step module logicalAnchors
        ⟨.value receiver, .methodReceiver name expressions env :: stack, logical⟩ globals) := by
  have same := bindMethod_keeps_heap module receiver name logical after outcome receiverInside executed
  subst after
  have paired := bindMethod_relocates logical physical rename layout.runtime module receiver name receiverInside
  rw [executed] at paired
  refine ⟨rfl, ?_, ?_⟩
  · cases outcome with
    | error exception =>
      simp [relocateState, relocateWork, List.map_cons, relocateFrame, step, run, executed, paired,
        protectGenerator, relocateStep, done, relocateCompletion, Except.map, Function.comp_def,
        relocateFrame_inGenerator]
      rfl
    | ok operation =>
      simp only [relocateState, relocateWork, List.map_cons, relocateFrame, step, run, executed, paired,
        Option.map_some, Except.map, protectGenerator_next, relocateStep]
      rw [← source operation rfl]
      exact congrArg Step.next (argumentsState_relocates rename logical physical operation env [] expressions stack)
  · apply protectGenerator_within
    cases outcome with
    | error exception =>
      simp only [run, executed, done, StepWithin, CompletionWithin]
      exact ⟨globalsInside, by intro value impossible; cases impossible⟩
    | ok operation =>
      simp only [run, executed, StepWithin]
      exact argumentsState_within logical operation env [] expressions stack
        (operationInside operation rfl) envInside (by simp) stackInside

/-- Binding a source method starts its argument evaluation with the original receiver retained. -/
theorem step_source_methodReceiver_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
    (receiver : Value) (name : String) (args : List Arg) (body : List Stmt)
    (expressions : List Expr) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (receiverInside : receiver.edge.Within logical.length) (envInside : EnvWithin logical.length env)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals)
    (source : ∀ statement ∈ body, StmtWithin 0 statement)
    (executed : bindMethod module receiver name logical = some (.ok (.method receiver args body), logical)) :
    step module physicalAnchors
        (relocateState rename physical ⟨.value receiver, .methodReceiver name expressions env :: stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.value receiver, .methodReceiver name expressions env :: stack, logical⟩ globals) ∧
      StepWithin (step module logicalAnchors
        ⟨.value receiver, .methodReceiver name expressions env :: stack, logical⟩ globals) := by
  apply (step_methodReceiver_relocates module logical physical rename layout logicalAnchors physicalAnchors
    receiver name expressions env stack globals receiverInside envInside stackInside globalsInside
    (.ok (.method receiver args body)) logical executed ?_ ?_).2
  · intro operation success
    cases success
    exact ⟨receiverInside, fun statement member => (source statement member).mono (Nat.zero_le _)⟩
  · intro operation success
    cases success
    simp only [relocateRuntimeOperation, relocateOperation, relocateBody_source rename body source]

theorem step_attribute_expression_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (base : Expr) (name : String) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors (relocateState rename physical ⟨.expr (.attribute base name) env, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.expr (.attribute base name) env, stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, step, protectGenerator_next, relocateStep, List.map_cons, relocateFrame]

theorem step_augmentAttribute_relocates (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout logical physical rename) (logicalAnchors physicalAnchors : Nat)
    (receiver : Value) (name : String) (op : BinOp) (right : Expr) (rest : List Stmt) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals)
    (receiverInside : receiver.edge.Within logical.length) (envInside : EnvWithin logical.length env)
    (restInside : ∀ statement ∈ rest, StmtWithin logical.length statement)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals)
    (outcome : Except ExceptionObject Value) (after : Mutable.Heap)
    (executed : getAttribute module receiver name logical = some (outcome, after)) :
    after = logical ∧
      step module physicalAnchors
          (relocateState rename physical ⟨.value receiver, .augmentAttribute name op right rest env :: stack, logical⟩)
          (relocateGlobals rename globals) =
        relocateStep rename physical physicalAnchors
          (step module logicalAnchors ⟨.value receiver, .augmentAttribute name op right rest env :: stack, logical⟩ globals) ∧
      StepWithin (step module logicalAnchors
        ⟨.value receiver, .augmentAttribute name op right rest env :: stack, logical⟩ globals) := by
  have effect := layout.readField receiver name receiverInside outcome after
    (getAttribute_readField module logical after receiver name outcome executed)
  have same := effect.2.2.1
  subst after
  have paired := getAttribute_relocates logical physical rename layout.runtime module receiver name receiverInside
  rw [executed] at paired
  refine ⟨rfl, ?_, ?_⟩
  · cases outcome <;>
      simp [relocateState, relocateWork, List.map_cons, relocateFrame, step, run, executed, paired,
        protectGenerator, relocateStep, done, relocateCompletion, Except.map, Function.comp_def,
        relocateFrame_inGenerator]
    rfl
  · apply protectGenerator_within
    cases outcome with
    | error exception =>
      simp only [run, executed, done, StepWithin, CompletionWithin]
      exact ⟨globalsInside, by intro value impossible; cases impossible⟩
    | ok previous =>
      simp only [run, executed, StepWithin]
      refine ⟨envInside, ?_⟩
      intro frame member
      rcases List.mem_cons.mp member with rfl | member
      · simpa only [FrameWithin] using effect.2.2.2 previous rfl
      · rcases List.mem_cons.mp member with rfl | member
        · simpa only [FrameWithin] using And.intro receiverInside (And.intro envInside restInside)
        · exact stackInside frame member

end FormalSW.PyAst.HeapCalls.Relocation
