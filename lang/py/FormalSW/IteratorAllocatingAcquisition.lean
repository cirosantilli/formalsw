import lang.py.FormalSW.IteratorAllocatingRun
import lang.py.FormalSW.IteratorAcquisitionIsolation

namespace FormalSW.PyAst.IteratorCalls
open HeapCalls HeapCalls.Relocation Mutable.Relocation
set_option Elab.async false

/-- Successful acquisition may allocate and return a different iterator. -/
def AllocatingAcquireRun (module : Module) (choices : ChoiceSchedule) (receiver : Mutable.Value)
    (before : Mutable.Heap) (used : Nat) (iterator : Mutable.Value) (after : Mutable.Heap) (finalUsed : Nat) : Prop :=
  ∃ operation advance, receiver.edge.Within before.length ∧ isInstance before receiver = true ∧
    ProtocolCalls.iterMethod module receiver before = some (.ok operation, before) ∧
    AllocatingTrace module before.length choices [] before
      (.running ⟨⟨.operation operation [], [], before⟩, used⟩ []) after
      (.completed (.ok ⟨.ok iterator, [], after, before.length⟩) finalUsed []) ∧
    ProtocolCalls.nextMethod module iterator after = some (.ok (some advance), after)

theorem AllocatingAcquireRun.acquireRun {module : Module} {choices : ChoiceSchedule} {receiver iterator : Mutable.Value}
    {before after : Mutable.Heap} {used finalUsed : Nat}
    (ran : AllocatingAcquireRun module choices receiver before used iterator after finalUsed) :
    AcquireRun module choices receiver before used iterator after finalUsed := by
  obtain ⟨operation, advance, inside, isObject, bound, executed, valid⟩ := ran
  exact ⟨operation, advance, inside, isObject, bound, executed.reaches, valid⟩

theorem AcquireRun.allocating_of_noGrowth {module : Module} {choices : ChoiceSchedule} {receiver iterator : Mutable.Value}
    {before after : Mutable.Heap} {used finalUsed : Nat}
    (ran : AcquireRun module choices receiver before used iterator after finalUsed)
    (noGrowth : after.length = before.length) :
    AllocatingAcquireRun module choices receiver before used iterator after finalUsed := by
  obtain ⟨operation, advance, inside, isObject, bound, executed, valid⟩ := ran
  exact ⟨operation, advance, inside, isObject, bound, .stable rfl rfl noGrowth executed, valid⟩

theorem AllocatingAcquireRun.for_name_isolated {module : Module} {choices : ChoiceSchedule} {receiver iterator : Mutable.Value}
    {before after : Mutable.Heap} {used finalUsed : Nat}
    (ran : AllocatingAcquireRun module choices receiver before used iterator after finalUsed)
    (source : Relocation.ModuleSource module) (physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout before physical rename) (anchors : Nat) :
    ∃ other nextMap, Relocation.ExtendedLayout before.length physical.length rename after other nextMap ∧
      (∀ address object, object ≠ .tuple [] → PrivateLayout before physical rename address object →
        PrivateLayout after other nextMap address object) ∧
      ∀ loop resumes inputName, loop.env inputName = some (relocateValue rename receiver) →
        Reaches module anchors choices []
          (.running ⟨⟨.block (.forIn (.name loop.name) (.name inputName) loop.body loop.otherwise :: loop.following)
            loop.env, loop.stack, physical⟩, used⟩ resumes)
          (.running ⟨⟨.block (loopCode loop (relocateValue nextMap iterator) :: loop.following)
            loop.env, loop.stack, other⟩, finalUsed⟩ resumes) := by
  have iteratorInside := (ran.acquireRun.effects source layout.closed).2.2
  obtain ⟨operation, advance, inside, isObject, bound, executed, valid⟩ := ran
  have method := Relocation.iterMethod_source module receiver before before operation source bound
  obtain ⟨other, nextMap, extended, _, kept, called⟩ := executed.isolated source physical rename anchors layout
    ⟨⟨method.within before.length inside, by simp⟩, by simp, by simp⟩ (by simp [GlobalsWithin])
  have moved := Relocation.iterMethod_runtime_relocates layout.runtime module receiver source inside
  rw [bound] at moved
  simp only [Option.map, Except.map] at moved
  have nextMoved := Relocation.nextMethod_runtime_relocates extended.layout.runtime module iterator source iteratorInside
  rw [valid] at nextMoved
  simp only [Option.map, Except.map] at nextMoved
  have instanceMoved : isInstance physical (relocateValue rename receiver) = true :=
    (Relocation.isInstance_relocates layout.runtime receiver inside).trans isObject
  refine ⟨other, nextMap, extended, kept, ?_⟩
  intro loop resumes inputName getInput
  apply Reaches.next (following := .running
    ⟨⟨.expr (.name inputName) loop.env,
      .sequence loop.name loop.body loop.otherwise loop.following loop.env :: loop.stack, physical⟩, used⟩ resumes) rfl
  apply (Reaches.of_heap (Evaluates.lookup getInput anchors _) resumes).trans
  apply Reaches.next (following := .running
    ⟨⟨.operation (relocateRuntimeOperation rename operation) [], [], physical⟩, used⟩ (.acquire loop :: resumes))
  · simp [step, intercept, instanceMoved, enter, moved]
  · apply acquired (operation := relocateRuntimeOperation nextMap advance) (valid := nextMoved)
    simpa only [Relocation.relocateState, Relocation.relocateCore, HeapCalls.Relocation.relocateState,
      relocateWork, List.map_nil, Except.map, relocateCompletion, relocateGlobals, appendResumes, List.nil_append] using
      called.append_resumes (.acquire loop :: resumes)

end FormalSW.PyAst.IteratorCalls
