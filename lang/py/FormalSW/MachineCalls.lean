import lang.py.FormalSW.MachineAllocation

/-! Call entry retains argument aliases, lexical scope, and suspended execution. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

@[simp] theorem relocateSource_id (source : SequenceSource) : relocateSource id source = source := by
  cases source <;> rfl

@[simp] theorem relocateStmt_id (statement : Stmt) : relocateStmt id statement = statement := by
  have sourceId : relocateSource id = id := funext relocateSource_id
  induction statement using Stmt.rec
    (motive_2 := fun body => body.map (relocateStmt id) = body) <;>
    simp_all [relocateStmt]

/-- Source definitions contain no live heap addresses. -/
theorem relocateStmt_source (rename : Nat → Nat) (statement : Stmt) (source : StmtWithin 0 statement) :
    relocateStmt rename statement = statement := by
  rw [relocateStmt_congr rename id 0 statement (by omega) source, relocateStmt_id]

theorem relocateBody_source (rename : Nat → Nat) (body : List Stmt)
    (source : ∀ statement ∈ body, StmtWithin 0 statement) : body.map (relocateStmt rename) = body := by
  have same := List.map_congr_left (fun statement member => relocateStmt_source rename statement (source statement member))
  simpa using same

theorem assignedLocals_forIn (target iterable : Expr) (body otherwise : List Stmt) :
    assignedLocals (.forIn target iterable body otherwise) =
      targetLocals target ++ blockLocals body ++ blockLocals otherwise := by
  cases target <;> first | rfl | simp [assignedLocals, targetLocals]

theorem assignedLocals_relocate (rename : Nat → Nat) (statement : Stmt) :
    assignedLocals (relocateStmt rename statement) = assignedLocals statement := by
  induction statement using Stmt.rec
    (motive_2 := fun body => blockLocals (body.map (relocateStmt rename)) = blockLocals body) with
  | forIn target iterable body otherwise bodyIH otherwiseIH =>
    rw [relocateStmt, assignedLocals_forIn, assignedLocals_forIn, bodyIH, otherwiseIH]
  | _ =>
    simp only [relocateStmt, List.map_nil, List.map_cons] <;>
      first | rfl | simp_all only [assignedLocals, blockLocals]

theorem blockLocals_relocate (rename : Nat → Nat) (body : List Stmt) :
    blockLocals (body.map (relocateStmt rename)) = blockLocals body := by
  induction body with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, blockLocals, assignedLocals_relocate, ih]

theorem executableBody_relocate (rename : Nat → Nat) (body : List Stmt) :
    executableBody (body.map (relocateStmt rename)) = (executableBody body).map (relocateStmt rename) := by
  cases body with
  | nil => rfl
  | cons head tail =>
    cases head with
    | expr expression =>
      cases expression with
      | constant constant => cases constant <;> simp only [List.map_cons, relocateStmt, executableBody]
      | _ => simp only [List.map_cons, relocateStmt, executableBody]
    | _ => simp only [List.map_cons, relocateStmt, executableBody]

theorem executableBody_within (limit : Nat) (body : List Stmt)
    (inside : ∀ statement ∈ body, StmtWithin limit statement) :
    ∀ statement ∈ executableBody body, StmtWithin limit statement := by
  unfold executableBody
  split
  · intro statement member
    exact inside statement (by simp [member])
  · exact inside

theorem zip_values_relocate (rename : Nat → Nat) (names : List String) (values : List Value) :
    names.zip (values.map (relocateValue rename)) =
      (names.zip values).map (fun pair => (pair.1, relocateValue rename pair.2)) := by
  induction names generalizing values with
  | nil => simp
  | cons head tail ih => cases values <;> simp [ih]

theorem argumentEnv_relocate (rename : Nat → Nat) (args : List Arg) (values : List Value) :
    argumentEnv args (values.map (relocateValue rename)) = relocateEnv rename (argumentEnv args values) := by
  funext name
  simp only [argumentEnv, zip_values_relocate, fields_lookup_relocate, relocateEnv]

theorem functionEnv_relocate (rename : Nat → Nat) (args : List Arg) (body : List Stmt)
    (values : List Value) (globals : Mutable.Globals) :
    functionEnv args (body.map (relocateStmt rename)) (values.map (relocateValue rename)) (relocateGlobals rename globals) =
      relocateEnv rename (functionEnv args body values globals) := by
  cases globals with
  | nil => exact argumentEnv_relocate rename args values
  | cons head tail =>
    funext name
    simp only [functionEnv, relocateGlobals, List.map_cons, blockLocals_relocate, argumentEnv_relocate, relocateEnv]
    split
    · rfl
    · split
      · rfl
      · exact fields_lookup_relocate rename (head :: tail) name

theorem lookup_within (limit : Nat) (fields : Mutable.Globals) (name : String) (value : Value)
    (inside : GlobalsWithin limit fields) (found : fields.lookup name = some value) : value.edge.Within limit := by
  obtain ⟨before, after, same, _⟩ := List.lookup_eq_some_iff.mp found
  exact inside (name, value) (by simp [same])

theorem zip_values_within (limit : Nat) (names : List String) (values : List Value)
    (inside : ∀ value ∈ values, value.edge.Within limit) : GlobalsWithin limit (names.zip values) := by
  induction names generalizing values with
  | nil => simp [GlobalsWithin]
  | cons head tail ih =>
    cases values with
    | nil => simp [GlobalsWithin]
    | cons value values =>
      have first := inside value (by simp)
      have rest := ih values (fun value member => inside value (by simp [member]))
      simpa [GlobalsWithin] using And.intro first rest

theorem argumentEnv_within (limit : Nat) (args : List Arg) (values : List Value)
    (inside : ∀ value ∈ values, value.edge.Within limit) : EnvWithin limit (argumentEnv args values) := by
  intro name value found
  exact lookup_within limit _ name value (zip_values_within limit (args.map Arg.name) values inside) found

theorem functionEnv_within (limit : Nat) (args : List Arg) (body : List Stmt) (values : List Value)
    (globals : Mutable.Globals) (inside : ∀ value ∈ values, value.edge.Within limit)
    (globalBounds : GlobalsWithin limit globals) : EnvWithin limit (functionEnv args body values globals) := by
  cases globals with
  | nil => exact argumentEnv_within limit args values inside
  | cons head tail =>
    intro name value found
    simp only [functionEnv] at found
    split at found
    · exact argumentEnv_within limit args values inside name value found
    · split at found
      · contradiction
      · exact lookup_within limit (head :: tail) name value globalBounds found

theorem completeArguments_relocate (rename : Nat → Nat) (args : List Arg) (values : List Value) :
    completeArguments args (values.map (relocateValue rename)) =
      (completeArguments args values).map (List.map (relocateValue rename)) := by
  induction args generalizing values with
  | nil => cases values <;> rfl
  | cons arg args ih =>
    cases values with
    | nil =>
      cases default : arg.defaultValue with
      | none => simp [completeArguments, default]
      | some value =>
        cases completed : completeArguments args [] with
        | none => simp [completeArguments, default, completed]
        | some tail =>
          have stable : tail = tail.map (relocateValue rename) := by
            simpa only [List.map_nil, completed, Option.map_some, Option.some.injEq] using ih []
          simpa [completeArguments, default, completed, relocateValue] using stable
    | cons value values =>
      cases completed : completeArguments args values <;> simp [completeArguments, ih, completed]

theorem completeArguments_within (limit : Nat) (args : List Arg) (values completed : List Value)
    (inside : ∀ value ∈ values, value.edge.Within limit)
    (executed : completeArguments args values = some completed) :
    ∀ value ∈ completed, value.edge.Within limit := by
  induction args generalizing values completed with
  | nil =>
    cases values <;> simp_all [completeArguments]
  | cons arg args ih =>
    cases values with
    | nil =>
      cases default : arg.defaultValue with
      | none => simp [completeArguments, default] at executed
      | some value =>
        cases rest : completeArguments args [] with
        | none => simp [completeArguments, default, rest] at executed
        | some tail =>
          have same : Mutable.Value.scalar value :: tail = completed := by simpa [completeArguments, default, rest] using executed
          subst completed
          have bounded := ih [] tail (by simp) rest
          simpa [Mutable.Value.edge, Graph.Edge.Within] using bounded
    | cons value values =>
      cases rest : completeArguments args values with
      | none => simp [completeArguments, rest] at executed
      | some tail =>
        have same : value :: tail = completed := by simpa [completeArguments, rest] using executed
        subst completed
        have bounded := ih values tail (fun value member => inside value (by simp [member])) rest
        simpa using And.intro (inside value (by simp)) bounded

theorem invokeMethod_relocate (rename : Nat → Nat) (logical physical : Mutable.Heap)
    (logicalAnchors physicalAnchors : Nat) (receiver : Value) (args : List Arg) (body : List Stmt)
    (values : List Value) (stack : List Frame) (globals : Mutable.Globals) :
    invokeMethod (globals := relocateGlobals rename globals) physicalAnchors (relocateValue rename receiver) args
        (body.map (relocateStmt rename)) (values.map (relocateValue rename)) (stack.map (relocateFrame rename)) physical =
      relocateStep rename physical physicalAnchors
        (invokeMethod (globals := globals) logicalAnchors receiver args body values stack logical) := by
  have other := completeArguments_relocate rename args (receiver :: values)
  simp only [List.map_cons] at other
  cases completed : completeArguments args (receiver :: values) <;>
    simp [invokeMethod, other, completed, executableBody_relocate, functionEnv_relocate,
      relocateStep, relocateState, relocateWork, done, relocateCompletion, Except.map]

theorem invokeMethod_within (heap : Mutable.Heap) (anchors : Nat) (receiver : Value) (args : List Arg)
    (body : List Stmt) (values : List Value) (stack : List Frame) (globals : Mutable.Globals) (next : State)
    (receiverInside : receiver.edge.Within heap.length)
    (valuesInside : ∀ value ∈ values, value.edge.Within heap.length)
    (bodyInside : ∀ statement ∈ body, StmtWithin heap.length statement)
    (stackInside : ∀ frame ∈ stack, FrameWithin heap.length frame)
    (globalsInside : GlobalsWithin heap.length globals)
    (stepped : invokeMethod (globals := globals) anchors receiver args body values stack heap = .next next) :
    StateWithin next := by
  cases completed : completeArguments args (receiver :: values) with
  | none => simp [invokeMethod, completed, done] at stepped
  | some filled =>
    have same : State.mk (.block (executableBody body) (functionEnv args body filled globals)) stack heap = next := by
      simpa [invokeMethod, completed] using stepped
    subst next
    have inputs : ∀ value ∈ receiver :: values, value.edge.Within heap.length := by simpa using And.intro receiverInside valuesInside
    exact ⟨⟨functionEnv_within heap.length args body filled globals
      (completeArguments_within heap.length args _ filled inputs completed) globalsInside,
      executableBody_within heap.length body bodyInside⟩, stackInside⟩

theorem step_method_relocate (module : Module) (rename : Nat → Nat) (logical physical : Mutable.Heap)
    (logicalAnchors physicalAnchors : Nat) (receiver : Value) (args : List Arg) (body : List Stmt)
    (values : List Value) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors
        (relocateState rename physical ⟨.operation (.method receiver args body) values, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.operation (.method receiver args body) values, stack, logical⟩ globals) := by
  simp only [relocateState, relocateWork, relocateRuntimeOperation, step]
  rw [invokeMethod_relocate rename logical physical logicalAnchors physicalAnchors receiver args body values stack globals]
  exact protectGenerator_relocates rename physical physicalAnchors stack _

theorem step_method_within (module : Module) (heap : Mutable.Heap) (anchors : Nat)
    (receiver : Value) (args : List Arg) (body : List Stmt) (values : List Value)
    (stack : List Frame) (globals : Mutable.Globals) (next : State)
    (inside : StateWithin ⟨.operation (.method receiver args body) values, stack, heap⟩)
    (globalsInside : GlobalsWithin heap.length globals)
    (stepped : step module anchors ⟨.operation (.method receiver args body) values, stack, heap⟩ globals = .next next) :
    StateWithin next := by
  have entered : invokeMethod (globals := globals) anchors receiver args body values stack heap = .next next := by
    cases completed : completeArguments args (receiver :: values) with
    | none => simp [step, invokeMethod, completed, done, protectGenerator] at stepped
    | some filled => simpa [step, invokeMethod, completed] using stepped
  exact invokeMethod_within heap anchors receiver args body values stack globals next inside.1.1.1 inside.1.2
    inside.1.1.2 inside.2 globalsInside entered

/-- Resolved source functions use the same definition in both executions. -/
theorem step_call_relocate (module : Module) (name : String) (args : List Arg) (body : List Stmt)
    (found : findFunctionIn module.body name = some (args, body))
    (source : ∀ statement ∈ body, StmtWithin 0 statement)
    (rename : Nat → Nat) (logical physical : Mutable.Heap) (logicalAnchors physicalAnchors : Nat)
    (values : List Value) (stack : List Frame) (globals : Mutable.Globals) :
    step module physicalAnchors (relocateState rename physical ⟨.operation (.call name) values, stack, logical⟩)
        (relocateGlobals rename globals) =
      relocateStep rename physical physicalAnchors
        (step module logicalAnchors ⟨.operation (.call name) values, stack, logical⟩ globals) := by
  have bodySame := relocateBody_source rename body source
  have executableSame := relocateBody_source rename (executableBody body) (executableBody_within 0 body source)
  have envSame (filled : List Value) := functionEnv_relocate rename args body filled globals
  simp only [bodySame] at envSame
  have other := completeArguments_relocate rename args values
  cases completed : completeArguments args values with
  | some filled =>
    simp [relocateState, relocateWork, relocateRuntimeOperation, relocateOperation, step, found, other, completed,
      relocateStep, envSame, executableSame]
  | none =>
    simp only [relocateState, relocateWork, relocateRuntimeOperation, relocateOperation, step, found, other, completed,
      Option.map_none]
    rw [← protectGenerator_relocates]
    rfl

theorem step_call_within (module : Module) (name : String) (args : List Arg) (body : List Stmt)
    (found : findFunctionIn module.body name = some (args, body))
    (source : ∀ statement ∈ body, StmtWithin 0 statement)
    (heap : Mutable.Heap) (anchors : Nat) (values : List Value) (stack : List Frame)
    (globals : Mutable.Globals) (next : State)
    (inside : StateWithin ⟨.operation (.call name) values, stack, heap⟩)
    (globalsInside : GlobalsWithin heap.length globals)
    (stepped : step module anchors ⟨.operation (.call name) values, stack, heap⟩ globals = .next next) :
    StateWithin next := by
  cases completed : completeArguments args values with
  | none => simp [step, found, completed, done, protectGenerator] at stepped
  | some filled =>
    have same : State.mk (.block (executableBody body) (functionEnv args body filled globals)) stack heap = next := by
      simpa [step, found, completed] using stepped
    subst next
    refine ⟨⟨functionEnv_within heap.length args body filled globals
      (completeArguments_within heap.length args values filled inside.1.2 completed) globalsInside, ?_⟩, inside.2⟩
    exact executableBody_within heap.length body (fun statement member => (source statement member).mono (Nat.zero_le _))

end FormalSW.PyAst.HeapCalls.Relocation
