import lang.py.FormalSW.IteratorAcquisitionIsolation

/-! Failed acquisition retains actual method effects and the consuming loop's exception boundary. -/
namespace FormalSW.PyAst.IteratorCalls
open HeapCalls HeapCalls.Relocation Mutable.Relocation
set_option Elab.async false

inductive AcquireFailure (module : Module) (choices : ChoiceSchedule) (receiver : Mutable.Value) :
    Mutable.Heap → Nat → ExceptionObject → Mutable.Heap → Nat → Prop where
  | binding {before used error}
      (inside : receiver.edge.Within before.length) (isObject : isInstance before receiver = true)
      (bound : ProtocolCalls.iterMethod module receiver before = some (.error error, before)) :
      AcquireFailure module choices receiver before used error before used
  | checked {before after used finalUsed error operation outcome}
      (inside : receiver.edge.Within before.length) (isObject : isInstance before receiver = true)
      (bound : ProtocolCalls.iterMethod module receiver before = some (.ok operation, before))
      (executed : Reaches module before.length choices []
        (.running ⟨⟨.operation operation [], [], before⟩, used⟩ [])
        (.completed (.ok ⟨outcome, [], after, before.length⟩) finalUsed []))
      (rejected : ProtocolCalls.iterFinish module ⟨outcome, [], after, before.length⟩ =
        some ⟨.error error, [], after, before.length⟩) :
      AcquireFailure module choices receiver before used error after finalUsed

theorem acquisition_method_effects {module : Module} {choices : ChoiceSchedule} {receiver : Mutable.Value}
    {before after : Mutable.Heap} {used finalUsed : Nat} {operation : Operation}
    {outcome : Except ExceptionObject Mutable.Value}
    (inside : receiver.edge.Within before.length)
    (bound : ProtocolCalls.iterMethod module receiver before = some (.ok operation, before))
    (executed : Reaches module before.length choices []
      (.running ⟨⟨.operation operation [], [], before⟩, used⟩ [])
      (.completed (.ok ⟨outcome, [], after, before.length⟩) finalUsed []))
    (source : Relocation.ModuleSource module) (closed : Closed before) :
    Closed after ∧ before.length ≤ after.length ∧
      ∀ value, outcome = .ok value → value.edge.Within after.length := by
  have method := Relocation.iterMethod_source module receiver before before operation source bound
  obtain ⟨finalHeap, _, _, _, grows, _, finalLayout, finalHeapFound, finalInside, _⟩ :=
    Relocation.reaches_isolated module choices before.length before.length [] source executed before before id
      (ExecutionLayout.refl before closed) rfl
      ⟨⟨method.within before.length inside, by simp⟩, by simp, by simp⟩ (by simp [GlobalsWithin])
  have equal : after = finalHeap := finalHeapFound
  subst finalHeap
  exact ⟨finalLayout.closed, grows, finalInside.2.1⟩

theorem AcquireFailure.effects {module : Module} {choices : ChoiceSchedule} {receiver : Mutable.Value}
    {before after : Mutable.Heap} {used finalUsed : Nat} {error : ExceptionObject}
    (ran : AcquireFailure module choices receiver before used error after finalUsed)
    (source : Relocation.ModuleSource module) (closed : Closed before) :
    Closed after ∧ before.length ≤ after.length := by
  cases ran with
  | binding => exact ⟨closed, Nat.le_refl _⟩
  | checked inside _ bound executed _ =>
      have effects := acquisition_method_effects inside bound executed source closed
      exact ⟨effects.1, effects.2.1⟩

theorem for_name_receiver {module : Module} {choices : ChoiceSchedule} {anchors used : Nat}
    (loop : Loop) (resumes : List Resume) (inputName : String) (physical : Mutable.Heap)
    (receiver : Mutable.Value) (getInput : loop.env inputName = some receiver) :
    Reaches module anchors choices []
      (.running ⟨⟨.block (.forIn (.name loop.name) (.name inputName) loop.body loop.otherwise :: loop.following)
        loop.env, loop.stack, physical⟩, used⟩ resumes)
      (.running ⟨⟨.value receiver,
        .sequence loop.name loop.body loop.otherwise loop.following loop.env :: loop.stack, physical⟩, used⟩ resumes) :=
  .next rfl (Reaches.of_heap (Evaluates.lookup getInput anchors _) resumes)

theorem AcquireFailure.for_name_isolated {module : Module} {choices : ChoiceSchedule} {receiver : Mutable.Value}
    {before after : Mutable.Heap} {used finalUsed : Nat} {error : ExceptionObject}
    (ran : AcquireFailure module choices receiver before used error after finalUsed)
    (source : Relocation.ModuleSource module) (physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout before physical rename) (noGrowth : after.length = before.length) (anchors : Nat) :
    ∃ other, ExecutionLayout after other rename ∧
      (∀ address object, PrivateLayout before physical rename address object →
        PrivateLayout after other rename address object) ∧
      ∀ (loop : Loop) (resumes : List Resume) (inputName : String),
        loop.env inputName = some (relocateValue rename receiver) →
        Reaches module anchors choices []
          (.running ⟨⟨.block (.forIn (.name loop.name) (.name inputName) loop.body loop.otherwise :: loop.following)
            loop.env, loop.stack, physical⟩, used⟩ resumes)
          (.completed (.ok ⟨.error (Calls.generatorException (loop.stack.any Frame.inGenerator) error),
            [], other, anchors⟩) finalUsed resumes) := by
  cases ran with
  | binding inside isObject bound =>
      have moved := Relocation.iterMethod_runtime_relocates layout.runtime module receiver source inside
      rw [bound] at moved
      simp only [Option.map, Except.map] at moved
      have instanceMoved := (Relocation.isInstance_relocates layout.runtime receiver inside).trans isObject
      refine ⟨physical, layout, fun _ _ initial => initial, ?_⟩
      intro loop resumes inputName getInput
      apply (for_name_receiver loop resumes inputName physical _ getInput).trans
      apply Reaches.next (following := .completed (.ok ⟨.error error, [], physical, anchors⟩) used
        (.acquire loop :: resumes))
      · simp [step, intercept, instanceMoved, enter, moved]
      · exact .next (by simp [step, resume, ProtocolCalls.iterFinish, propagate]) .refl
  | checked inside isObject bound executed rejected =>
      rename_i operation outcome
      have outcomeInside := (acquisition_method_effects inside bound executed source layout.closed).2.2
      have method := Relocation.iterMethod_source module receiver before before operation source bound
      obtain ⟨other, nextMap, extended, kept, called⟩ := Relocation.operation_completion_isolated
        module choices before physical rename before.length anchors used finalUsed operation outcome after []
          source layout (method.within before.length inside) (by simp [GlobalsWithin]) executed noGrowth
      have same : ∀ index < after.length, rename index = nextMap index := by
        intro index bounded
        exact (extended.agrees index (by omega)).symm
      have moved := Relocation.iterMethod_runtime_relocates layout.runtime module receiver source inside
      rw [bound] at moved
      simp only [Option.map, Except.map] at moved
      have checked := Relocation.iterFinish_relocates module ⟨outcome, [], after, before.length⟩
        other nextMap anchors extended.layout.runtime outcomeInside
      rw [rejected] at checked
      simp only [Option.map_some, relocateCompletion, relocateGlobals, List.map_nil, Except.map] at checked
      have instanceMoved := (Relocation.isInstance_relocates layout.runtime receiver inside).trans isObject
      refine ⟨other, extended.layout.congr same, fun address object initial => (kept address object initial).congr same, ?_⟩
      intro loop resumes inputName getInput
      apply (for_name_receiver loop resumes inputName physical _ getInput).trans
      apply Reaches.next (following := .running
        ⟨⟨.operation (relocateRuntimeOperation rename operation) [], [], physical⟩, used⟩ (.acquire loop :: resumes))
      · simp [step, intercept, instanceMoved, enter, moved]
      · apply (show Reaches module anchors choices [] _ _ from by
          simpa only [relocateGlobals, List.map_nil] using called (.acquire loop :: resumes)).trans
        exact .next (by simp [step, resume, checked, propagate, relocateCompletion, relocateGlobals, Except.map]) .refl

/-- Terminal failure transport permits allocation; its caller receives the final logical object graph. -/
theorem AcquireFailure.for_name_relocates {module : Module} {choices : ChoiceSchedule} {receiver : Mutable.Value}
    {before after : Mutable.Heap} {used finalUsed : Nat} {error : ExceptionObject}
    (ran : AcquireFailure module choices receiver before used error after finalUsed)
    (source : Relocation.ModuleSource module) (physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout before physical rename) (anchors : Nat) :
    ∃ other nextMap, Relocation.ExtendedLayout before.length physical.length rename after other nextMap ∧
      ∀ (loop : Loop) (resumes : List Resume) (inputName : String),
        loop.env inputName = some (relocateValue rename receiver) →
        Reaches module anchors choices []
          (.running ⟨⟨.block (.forIn (.name loop.name) (.name inputName) loop.body loop.otherwise :: loop.following)
            loop.env, loop.stack, physical⟩, used⟩ resumes)
          (.completed (.ok ⟨.error (Calls.generatorException (loop.stack.any Frame.inGenerator) error),
            [], other, anchors⟩) finalUsed resumes) := by
  cases ran with
  | binding inside isObject bound =>
      have moved := Relocation.iterMethod_runtime_relocates layout.runtime module receiver source inside
      rw [bound] at moved
      simp only [Option.map, Except.map] at moved
      have instanceMoved := (Relocation.isInstance_relocates layout.runtime receiver inside).trans isObject
      refine ⟨physical, rename, ⟨layout, Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl⟩, ?_⟩
      intro loop resumes inputName getInput
      apply (for_name_receiver loop resumes inputName physical _ getInput).trans
      apply Reaches.next (following := .completed (.ok ⟨.error error, [], physical, anchors⟩) used
        (.acquire loop :: resumes))
      · simp [step, intercept, instanceMoved, enter, moved]
      · exact .next (by simp [step, resume, ProtocolCalls.iterFinish, propagate]) .refl
  | checked inside isObject bound executed rejected =>
      rename_i operation outcome
      have outcomeInside := (acquisition_method_effects inside bound executed source layout.closed).2.2
      have method := Relocation.iterMethod_source module receiver before before operation source bound
      obtain ⟨other, nextMap, extended, called⟩ := Relocation.operation_completion_relocates
        module choices before physical rename before.length anchors used finalUsed operation outcome after []
          source layout (method.within before.length inside) (by simp [GlobalsWithin]) executed
      have moved := Relocation.iterMethod_runtime_relocates layout.runtime module receiver source inside
      rw [bound] at moved
      simp only [Option.map, Except.map] at moved
      have checked := Relocation.iterFinish_relocates module ⟨outcome, [], after, before.length⟩
        other nextMap anchors extended.layout.runtime outcomeInside
      rw [rejected] at checked
      simp only [Option.map_some, relocateCompletion, relocateGlobals, List.map_nil, Except.map] at checked
      have instanceMoved := (Relocation.isInstance_relocates layout.runtime receiver inside).trans isObject
      refine ⟨other, nextMap, extended, ?_⟩
      intro loop resumes inputName getInput
      apply (for_name_receiver loop resumes inputName physical _ getInput).trans
      apply Reaches.next (following := .running
        ⟨⟨.operation (relocateRuntimeOperation rename operation) [], [], physical⟩, used⟩ (.acquire loop :: resumes))
      · simp [step, intercept, instanceMoved, enter, moved]
      · apply (show Reaches module anchors choices [] _ _ from by
          simpa only [relocateGlobals, List.map_nil] using called (.acquire loop :: resumes)).trans
        exact .next (by simp [step, resume, checked, propagate, relocateCompletion, relocateGlobals, Except.map]) .refl

end FormalSW.PyAst.IteratorCalls
