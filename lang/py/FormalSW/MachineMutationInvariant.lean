import lang.py.FormalSW.MachineInvariant

/-! Shared mutations retain the execution invariant through successful and failed writes. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem result_preserves (logical physical logicalAfter physicalAfter : Mutable.Heap) (rename nextMap : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (action otherAction : Mutable.Eval Value)
    (stack : List Frame) (globals : Mutable.Globals) (outcome : Except ExceptionObject Value)
    (agree : ∀ address < logical.length, nextMap address = rename address)
    (grows : logical.length ≤ logicalAfter.length) (physicalGrows : physical.length ≤ physicalAfter.length)
    (layout : ExecutionLayout logicalAfter physicalAfter nextMap)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals)
    (valueInside : ∀ value, outcome = .ok value → value.edge.Within logicalAfter.length)
    (executed : action logical = some (outcome, logicalAfter))
    (other : otherAction physical = some (outcome.map (relocateValue nextMap), physicalAfter)) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical action stack globals)
      (result physicalAnchors physical otherAction (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  refine ⟨logicalAfter, physicalAfter, nextMap, agree, grows, physicalGrows, layout, ?_, ?_, ?_⟩
  · cases outcome <;> simp [result, run, executed, done, StepHeap]
  · exact result_within logicalAnchors logical logicalAfter action stack globals outcome executed grows valueInside stackInside globalsInside
  · exact result_extending_relocates rename nextMap logical physical logicalAfter physicalAfter logicalAnchors physicalAnchors
      action otherAction stack globals outcome agree stackInside globalsInside executed other

theorem Preserves.protectGenerator {logical physical : Mutable.Heap} {rename : Nat → Nat} {anchors : Nat}
    {left right : Step State Mutable.Completion}
    (preserved : Preserves logical physical rename anchors left right)
    (stack : List Frame) (inside : ∀ frame ∈ stack, FrameWithin logical.length frame) :
    Preserves logical physical rename anchors (protectGenerator stack left)
      (protectGenerator (stack.map (relocateFrame rename)) right) := by
  obtain ⟨logicalAfter, physicalAfter, nextMap, agree, grows, physicalGrows, layout, heap, bounded, paired⟩ := preserved
  refine ⟨logicalAfter, physicalAfter, nextMap, agree, grows, physicalGrows, layout,
    protectGenerator_heap logicalAfter stack left heap, protectGenerator_within stack left bounded, ?_⟩
  rw [paired, ← relocateStack_congr nextMap rename logical.length stack agree inside]
  exact protectGenerator_relocates nextMap physicalAfter anchors stack left

/-- Valid receivers leave only reserved attributes outside the stored-field model. -/
theorem writeField_unsupported_iff (heap : Mutable.Heap) (receiver value : Value) (name : String)
    (inside : receiver.edge.Within heap.length) :
    Mutable.writeField receiver name value heap = none ↔ name = "__class__" ∨ name = "__dict__" ∨ name = "__weakref__" := by
  by_cases special : name = "__class__" ∨ name = "__dict__" ∨ name = "__weakref__"
  · simp [Mutable.writeField, special, Mutable.unsupported]
  · cases receiver with
    | scalar scalar => simp [Mutable.writeField, Mutable.instanceData, special, Mutable.error]
    | ref address =>
      have found : heap[address]? = some heap[address] := List.getElem?_eq_getElem inside
      cases object : heap[address] with
      | dataInstance origin className frozen declared fields =>
        cases frozen <;> simp [Mutable.writeField, Mutable.instanceData, special, found, object, Mutable.error, Except.map]
      | _ => simp [Mutable.writeField, Mutable.instanceData, special, found, object, Mutable.error, Except.map]

theorem result_writeField_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (receiver value : Value) (name : String)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (receiverInside : receiver.edge.Within logical.length) (valueInside : value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (Mutable.writeField receiver name value) stack globals)
      (result physicalAnchors physical (Mutable.writeField (relocateValue rename receiver) name (relocateValue rename value))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  cases executed : Mutable.writeField receiver name value logical with
  | none =>
    have special := (writeField_unsupported_iff logical receiver value name receiverInside).mp executed
    have other : Mutable.writeField (relocateValue rename receiver) name (relocateValue rename value) physical = none := by
      simp [Mutable.writeField, special, Mutable.unsupported]
    apply Preserves.unchanged layout <;> simp [result, run, executed, other, StepHeap, StepWithin, relocateStep]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    obtain ⟨other, paired, retained, length, bounded⟩ := layout.writeField receiver name value receiverInside valueInside outcome after executed
    have physicalLength := (writeField_effect physical other (relocateValue rename receiver) name
      (relocateValue rename value) _ paired).length
    exact result_preserves logical physical after other rename rename logicalAnchors physicalAnchors _ _ stack globals outcome
      (fun _ _ => rfl) (Nat.le_of_eq length.symm) (Nat.le_of_eq physicalLength.symm) retained stackInside globalsInside bounded executed paired

theorem step_setField_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (receiver value : Value) (name : String) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation (.setField name value) [receiver], stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.setField name value) [receiver], stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation (.setField name value) [receiver], stack, logical⟩)
        (relocateGlobals rename globals)) := by
  exact (result_writeField_preserves logical physical rename logicalAnchors physicalAnchors receiver value name stack globals layout
    (inside.1.2 receiver (by simp)) inside.1.1 inside.2 globalsInside).protectGenerator stack inside.2

theorem step_writeAttribute_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (receiver value : Value) (name : String) (body : List Stmt) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .writeAttribute receiver name body env :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .writeAttribute receiver name body env :: stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.value value, .writeAttribute receiver name body env :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have saved := inside.2 _ (List.mem_cons_self ..)
  simp only [FrameWithin] at saved
  have remainder : ∀ frame ∈ .discard body env :: stack, FrameWithin logical.length frame := by
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [FrameWithin] using And.intro saved.2.1 saved.2.2
    · exact inside.2 frame (List.mem_cons_of_mem _ member)
  simpa only [step, relocateState, relocateWork, List.map_cons, relocateFrame] using
    (result_writeField_preserves logical physical rename logicalAnchors physicalAnchors receiver value name
    (.discard body env :: stack) globals layout saved.1 inside.1 remainder globalsInside).protectGenerator _ inside.2

/-- All list index values either update a slot or produce a modeled exception. -/
theorem setItem_list_total (heap : Mutable.Heap) (address : Nat) (items : List Value) (index value : Value)
    (found : heap[address]? = some (.list items)) :
    ∃ outcome after, Mutable.setItem (.ref address) index value heap = some (outcome, after) ∧ after.length = heap.length := by
  obtain ⟨outcome, indexed, _⟩ := index_total items index heap
  cases outcome with
  | error exception =>
    exact ⟨.error exception, heap, by simp [Mutable.setItem, found, indexed, Mutable.eval_bind], rfl⟩
  | ok position =>
    refine ⟨.ok (.scalar .none), heap.set address (.list (items.set position value)), ?_, by simp⟩
    simp [Mutable.setItem, found, indexed, Mutable.eval_bind, Except.map]

theorem setItem_list_length (heap after : Mutable.Heap) (address : Nat) (items : List Value) (index value : Value)
    (outcome : Except ExceptionObject Value) (found : heap[address]? = some (.list items))
    (executed : Mutable.setItem (.ref address) index value heap = some (outcome, after)) : after.length = heap.length := by
  obtain ⟨result, actual, completed, length⟩ := setItem_list_total heap address items index value found
  rw [executed] at completed
  have same : after = actual := congrArg Prod.snd (Option.some.inj completed)
  exact same ▸ length

theorem step_setItem_list_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (address : Nat) (items : List Value) (index value : Value)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (found : logical[address]? = some (.list items)) (valueInside : value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.setItem value) [.ref address, index], stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation (.setItem value) [.ref address, index], stack, logical⟩)
        (relocateGlobals rename globals)) := by
  obtain ⟨outcome, after, executed, _⟩ := setItem_list_total logical address items index value found
  obtain ⟨other, paired, retained, length, bounded⟩ := layout.setItem_list address items index value found valueInside outcome after executed
  have physicalFound : physical[rename address]? = some (.list (items.map (relocateValue rename))) := layout.runtime.lookup address _ found
  have physicalLength := setItem_list_length physical other (rename address) _ (relocateValue rename index)
    (relocateValue rename value) _ physicalFound paired
  exact (result_preserves logical physical after other rename rename logicalAnchors physicalAnchors _ _ stack globals outcome
    (fun _ _ => rfl) (Nat.le_of_eq length.symm) (Nat.le_of_eq physicalLength.symm) retained stackInside globalsInside bounded executed paired).protectGenerator stack stackInside

theorem step_append_list_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (address : Nat) (items : List Value) (value : Value)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (found : logical[address]? = some (.list items)) (valueInside : value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.append address) [value], stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation (.append address) [value], stack, logical⟩)
        (relocateGlobals rename globals)) := by
  obtain ⟨retained, first, second, bounded, _⟩ := step_append_list_relocates module logical physical rename layout logicalAnchors physicalAnchors
    address items value stack globals found valueInside stackInside globalsInside
  refine ⟨logical.set address (.list (items ++ [value])), physical.set (rename address) (.list ((items ++ [value]).map (relocateValue rename))),
    rename, fun _ _ => rfl, by simp, by simp, retained, ?_, ?_, ?_⟩
  · rw [first]; rfl
  · rw [first]; exact bounded
  · rw [first]; exact second

theorem step_discard_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (body : List Stmt) (env : Env)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .discard body env :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .discard body env :: stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.value value, .discard body env :: stack, logical⟩)
        (relocateGlobals rename globals)) :=
  Preserves.unchanged layout rfl (StateWithin.discard logical value body env stack inside)
    (step_discard_relocates module logical physical rename logicalAnchors physicalAnchors value body env stack globals)


/-- Stored-field reads retain aliases; failed or unsupported lookup stays observable. -/
theorem step_attribute_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (receiver : Value) (name : String) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value receiver, .attribute name :: stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value receiver, .attribute name :: stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.value receiver, .attribute name :: stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have paired := getAttribute_relocates logical physical rename layout.runtime module receiver name inside.1
  have stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame :=
    fun frame member => inside.2 frame (List.mem_cons_of_mem _ member)
  cases executed : getAttribute module receiver name logical with
  | none =>
    simp only [executed, Option.map_none] at paired
    apply Preserves.unchanged layout <;>
      simp [step, result, run, executed, paired, protectGenerator, StepHeap, StepWithin, relocateState,
        relocateWork, relocateFrame, relocateStep]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have effect := layout.readField receiver name inside.1 outcome after (getAttribute_readField module logical after receiver name outcome executed)
    have same := effect.2.2.1
    subst after
    simp only [executed, Option.map_some] at paired
    simpa only [step, relocateState, relocateWork, List.map_cons, relocateFrame] using
      (result_preserves logical physical logical physical rename rename logicalAnchors physicalAnchors
      _ _ stack globals outcome (fun _ _ => rfl) (Nat.le_refl _) (Nat.le_refl _) layout stackInside globalsInside
      effect.2.2.2 executed paired).protectGenerator (.attribute name :: stack) inside.2


theorem step_assignAttribute_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value : Value) (base : Expr) (name : String) (body : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.value value, .assignAttribute base name body env :: stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.value value, .assignAttribute base name body env :: stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.value value, .assignAttribute base name body env :: stack, logical⟩)
        (relocateGlobals rename globals)) :=
  Preserves.unchanged layout rfl (StateWithin.assignAttribute logical value base name body env stack inside)
    (step_assignAttribute_relocates module logical physical rename logicalAnchors physicalAnchors value base name body env stack globals)

/-- Attribute assignment evaluates the value before evaluating its receiver. -/
theorem step_assignField_start_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (value base : Expr) (name : String) (body : List Stmt)
    (env : Env) (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.block (.assign [.attribute base name] value :: body) env, stack, logical⟩) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.block (.assign [.attribute base name] value :: body) env, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.block (.assign [.attribute base name] value :: body) env, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  apply Preserves.unchanged layout
  · rfl
  · refine ⟨inside.1.1, ?_⟩
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simp only [FrameWithin]
      exact ⟨inside.1.1, fun statement member => inside.1.2 statement (List.mem_cons_of_mem _ member)⟩
    · exact inside.2 frame member
  · simp only [step, relocateState, relocateWork, List.map_cons, relocateStmt, relocateFrame, protectGenerator_next, relocateStep]

end FormalSW.PyAst.HeapCalls.Relocation
