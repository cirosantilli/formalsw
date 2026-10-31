import lang.py.FormalSW.MethodBindingInvariant

/-! Method binding and attribute evaluation retain caller states for every modeled outcome. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem bindMethod_within (module : Module) (heap after : Mutable.Heap)
    (receiver : Value) (name : String) (operation : Operation)
    (source : ∀ statement ∈ module.body, StmtWithin 0 statement)
    (inside : receiver.edge.Within heap.length)
    (executed : bindMethod module receiver name heap = some (.ok operation, after)) :
    BoundMethodWithin heap.length operation := by
  by_cases reverse : name = "$formalsw.sort.reverse"
  · subst name
    rw [bindMethod_reverse] at executed
    cases bound : bindMethod module receiver "sort" heap with
    | none => simp [bound, Mutable.eval_bind] at executed
    | some pair =>
      rcases pair with ⟨outcome, middle⟩
      have unchanged := bindMethod_keeps_heap module receiver "sort" heap middle outcome inside bound
      subst middle
      cases outcome with
      | error exception => simp [bound, Mutable.eval_bind] at executed
      | ok selected =>
        have bounded := bindMethod_ordinary_within module heap heap receiver "sort" selected source inside (by decide) bound
        cases selected <;> simp [bound, Mutable.eval_bind, Mutable.unsupported] at executed
        rcases executed with ⟨rfl, rfl⟩
        exact ⟨bounded.1, fun _ => rfl⟩
  · exact bindMethod_ordinary_within module heap after receiver name operation source inside reverse executed

theorem step_methodReceiver_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (receiver : Value) (name : String) (expressions : List Expr)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (source : ∀ statement ∈ module.body, StmtWithin 0 statement)
    (inside : StateWithin ⟨.value receiver, .methodReceiver name expressions env :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value receiver, .methodReceiver name expressions env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value receiver, .methodReceiver name expressions env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have paired := bindMethod_relocates logical physical rename layout.runtime module receiver name inside.1
  have envInside := inside.2 (.methodReceiver name expressions env) (by simp)
  simp only [FrameWithin] at envInside
  have stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame :=
    fun frame member => inside.2 frame (by simp [member])
  cases executed : bindMethod module receiver name logical with
  | none =>
    simp only [executed, Option.map_none] at paired
    apply Preserves.unchanged layout <;>
      simp [step, run, executed, paired, protectGenerator, StepHeap, StepWithin,
        relocateState, relocateWork, relocateFrame, relocateStep]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have same := bindMethod_keeps_heap module receiver name logical after outcome inside.1 executed
    subst after
    have bounded : ∀ selected, outcome = .ok selected → BoundMethodWithin logical.length selected := by
      intro selected selectedEq
      exact bindMethod_within module logical logical receiver name selected source inside.1 (selectedEq ▸ executed)
    have retained := step_methodReceiver_relocates module logical physical rename layout logicalAnchors physicalAnchors
      receiver name expressions env stack globals inside.1 envInside stackInside globalsInside outcome logical executed
      (fun selected selectedEq => (bounded selected selectedEq).1)
      (fun selected selectedEq => (bounded selected selectedEq).2 rename)
    apply Preserves.unchanged layout _ retained.2.2 retained.2.1
    apply protectGenerator_heap
    cases outcome with
    | error exception => simp [run, executed, done, StepHeap]
    | ok selected => simpa only [run, executed, StepHeap] using argumentsState_heap logical selected env [] expressions stack

theorem step_attribute_expression_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (base : Expr) (name : String) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.expr (.attribute base name) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.expr (.attribute base name) env, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.expr (.attribute base name) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · rfl
  · refine ⟨inside.1, ?_⟩
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simp [FrameWithin]
    · exact inside.2 frame member
  · exact step_attribute_expression_relocates module logical physical rename logicalAnchors physicalAnchors base name env stack globals

theorem step_augmentAttribute_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (receiver : Value) (name : String) (op : BinOp) (right : Expr)
    (rest : List Stmt) (env : Env) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value receiver, .augmentAttribute name op right rest env :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value receiver, .augmentAttribute name op right rest env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value receiver, .augmentAttribute name op right rest env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have paired := getAttribute_relocates logical physical rename layout.runtime module receiver name inside.1
  have saved := inside.2 (.augmentAttribute name op right rest env) (by simp)
  simp only [FrameWithin] at saved
  have stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame :=
    fun frame member => inside.2 frame (by simp [member])
  cases executed : getAttribute module receiver name logical with
  | none =>
    simp only [executed, Option.map_none] at paired
    apply Preserves.unchanged layout <;>
      simp [step, run, executed, paired, protectGenerator, StepHeap, StepWithin,
        relocateState, relocateWork, relocateFrame, relocateStep]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have retained := step_augmentAttribute_relocates module logical physical rename layout logicalAnchors physicalAnchors
      receiver name op right rest env stack globals inside.1 saved.1 saved.2 stackInside globalsInside outcome after executed
    have same := retained.1
    subst after
    apply Preserves.unchanged layout _ retained.2.2 retained.2.1
    apply protectGenerator_heap
    cases outcome <;> simp [run, executed, done, StepHeap]

/-- The append shortcut performs the same binding as an ordinary method call. -/
theorem step_appendReceiver_eq (module : Module) (heap : Mutable.Heap) (anchors : Nat)
    (receiver : Value) (item : Expr) (env : Env) (stack : List Frame) (globals : Mutable.Globals) :
    step module anchors ⟨.value receiver, .appendReceiver item env :: stack, heap⟩ globals =
      step module anchors ⟨.value receiver, .methodReceiver "append" [item] env :: stack, heap⟩ globals := by
  cases receiver with
  | scalar value =>
    cases value <;> simp [step, bindMethod, Mutable.error, run, done, protectGenerator, Frame.inGenerator]
  | ref address =>
    cases found : heap[address]? with
    | none => simp [step, found, bindMethod, Mutable.appendReceiver, Mutable.unsupported, run]
    | some object =>
      cases object with
      | «instance» origin name fields | dataInstance origin name frozen declared fields =>
        simp [step, found, protectGenerator, Frame.inGenerator]
      | _ => simp [step, found, bindMethod, Mutable.appendReceiver, Mutable.error, run, done,
          protectGenerator, Frame.inGenerator]

theorem step_appendReceiver_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (receiver : Value) (item : Expr) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (source : ∀ statement ∈ module.body, StmtWithin 0 statement)
    (inside : StateWithin ⟨.value receiver, .appendReceiver item env :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value receiver, .appendReceiver item env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value receiver, .appendReceiver item env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have bound : StateWithin ⟨.value receiver, .methodReceiver "append" [item] env :: stack, logical⟩ := by
    simpa only [StateWithin, List.mem_cons, forall_eq_or_imp, FrameWithin] using inside
  simpa only [relocateState, relocateWork, List.map_cons, relocateFrame, step_appendReceiver_eq] using
    step_methodReceiver_preserves module logical physical rename logicalAnchors physicalAnchors
      receiver "append" [item] env stack globals layout source bound globalsInside

theorem step_addReceiver_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (receiver : Value) (item : Expr) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (source : ∀ statement ∈ module.body, StmtWithin 0 statement)
    (inside : StateWithin ⟨.value receiver, .addReceiver item env :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value receiver, .addReceiver item env :: stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.value receiver, .addReceiver item env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have bound : StateWithin ⟨.value receiver, .methodReceiver "add" [item] env :: stack, logical⟩ := by
    simpa only [StateWithin, List.mem_cons, forall_eq_or_imp, FrameWithin] using inside
  have retained := step_methodReceiver_preserves module logical physical rename logicalAnchors physicalAnchors
    receiver "add" [item] env stack globals layout source bound globalsInside
  cases receiver with
  | scalar value =>
    cases value <;> simpa [step, relocateState, relocateWork, relocateFrame, relocateValue, bindMethod,
      Mutable.error, run, done, protectGenerator, Frame.inGenerator] using retained
  | ref address =>
    have addressInside : address < logical.length := inside.1
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem addressInside
    have moved := layout.runtime.lookup address _ found
    cases object : logical[address] with
    | list items | bytearray bytes =>
      simp only [object, relocateObject] at moved
      apply Preserves.unchanged layout
      · simp [step, found, object, Mutable.addReceiver, Mutable.error, run, done, protectGenerator, StepHeap]
      · simp [step, found, object, Mutable.addReceiver, Mutable.error, run, done, protectGenerator,
          StepWithin, CompletionWithin, globalsInside, Calls.generatorException]
      · simp [step, found, object, moved, Mutable.addReceiver, Mutable.error, run, done, protectGenerator,
          relocateState, relocateWork, relocateValue, relocateFrame, relocateStep, relocateCompletion,
          Frame.inGenerator, Except.map, Calls.generatorException]
    | _ =>
      simp only [object, relocateObject] at moved
      simpa [step, found, object, moved, relocateState, relocateWork, relocateFrame, relocateValue,
        bindMethod, Mutable.addReceiver, Mutable.error, run, done, protectGenerator, Frame.inGenerator] using retained

theorem step_notCallable_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation .notCallable values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation .notCallable values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation .notCallable values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  exact (result_preserves logical physical logical physical rename rename logicalAnchors physicalAnchors
    (primitive .notCallable values) (primitive .notCallable (values.map (relocateValue rename)))
    stack globals (.error ⟨"TypeError", []⟩) (fun _ _ => rfl) (Nat.le_refl _) (Nat.le_refl _) layout inside.2
    globalsInside (by intro value impossible; cases impossible) rfl rfl).protectGenerator stack inside.2

end FormalSW.PyAst.HeapCalls.Relocation
