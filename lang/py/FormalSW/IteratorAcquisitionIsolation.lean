import lang.py.FormalSW.IteratorTraversal

/-! Actual acquisition methods preserve private consumer storage before iteration begins. -/
namespace FormalSW.PyAst.Mutable.Relocation

theorem ExecutionLayout.append_private_nonempty {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (object : Object) (nonempty : object ≠ .tuple []) :
    ExecutionLayout logical (physical ++ [object]) rename :=
  layout.preserves (layout.runtime.append_private [object]) (emptyTupleAddress_append_nonempty physical object nonempty)

theorem ExecutionLayout.new_private_cell {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (object : Object) (nonempty : object ≠ .tuple []) :
    PrivateLayout logical (physical ++ [object]) rename physical.length object := by
  refine ⟨layout.append_private_nonempty object nonempty, by simp [SavedCell], ?_⟩
  intro index inside
  exact Nat.ne_of_lt (layout.runtime.bound index inside)

end FormalSW.PyAst.Mutable.Relocation

namespace FormalSW.PyAst.IteratorCalls
open HeapCalls HeapCalls.Relocation Mutable.Relocation
set_option Elab.async false

def AcquireRun (module : Module) (choices : ChoiceSchedule) (receiver : Mutable.Value)
    (before : Mutable.Heap) (used : Nat) (iterator : Mutable.Value) (after : Mutable.Heap) (finalUsed : Nat) : Prop :=
  ∃ operation advance, receiver.edge.Within before.length ∧ isInstance before receiver = true ∧
    ProtocolCalls.iterMethod module receiver before = some (.ok operation, before) ∧
    Reaches module before.length choices []
      (.running ⟨⟨.operation operation [], [], before⟩, used⟩ [])
      (.completed (.ok ⟨.ok iterator, [], after, before.length⟩) finalUsed []) ∧
    ProtocolCalls.nextMethod module iterator after = some (.ok (some advance), after)

theorem AcquireRun.effects {module : Module} {choices : ChoiceSchedule} {receiver iterator : Mutable.Value}
    {before after : Mutable.Heap} {used finalUsed : Nat}
    (ran : AcquireRun module choices receiver before used iterator after finalUsed)
    (source : Relocation.ModuleSource module) (closed : Closed before) :
    Closed after ∧ before.length ≤ after.length ∧ iterator.edge.Within after.length := by
  obtain ⟨operation, _, inside, _, bound, executed, _⟩ := ran
  have method := Relocation.iterMethod_source module receiver before before operation source bound
  obtain ⟨finalHeap, _, _, _, grows, _, finalLayout, finalStateHeap, finalInside, _⟩ :=
    Relocation.reaches_isolated module choices before.length before.length [] source executed before before id
      (ExecutionLayout.refl before closed) rfl
      ⟨⟨method.within before.length inside, by simp⟩, by simp, by simp⟩ (by simp [GlobalsWithin])
  have equal : after = finalHeap := finalStateHeap
  subst finalHeap
  exact ⟨finalLayout.closed, grows, finalInside.2.1 iterator rfl⟩

theorem AcquireRun.for_name_isolated {module : Module} {choices : ChoiceSchedule} {receiver iterator : Mutable.Value}
    {before after : Mutable.Heap} {used finalUsed : Nat}
    (ran : AcquireRun module choices receiver before used iterator after finalUsed)
    (source : Relocation.ModuleSource module) (physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout before physical rename) (noGrowth : after.length = before.length) (anchors : Nat) :
    ∃ other, ExecutionLayout after other rename ∧
      (∀ address object, PrivateLayout before physical rename address object →
        PrivateLayout after other rename address object) ∧
      ∀ loop resumes inputName, loop.env inputName = some (relocateValue rename receiver) →
        Reaches module anchors choices []
          (.running ⟨⟨.block (.forIn (.name loop.name) (.name inputName) loop.body loop.otherwise :: loop.following)
            loop.env, loop.stack, physical⟩, used⟩ resumes)
          (.running ⟨⟨.block (loopCode loop (relocateValue rename iterator) :: loop.following)
            loop.env, loop.stack, other⟩, finalUsed⟩ resumes) := by
  have iteratorInside := (ran.effects source layout.closed).2.2
  obtain ⟨operation, advance, inside, isObject, bound, executed, valid⟩ := ran
  have method := Relocation.iterMethod_source module receiver before before operation source bound
  obtain ⟨other, nextMap, extended, kept, called⟩ := Relocation.operation_completion_isolated
    module choices before physical rename before.length anchors used finalUsed operation (.ok iterator) after []
      source layout (method.within before.length inside) (by simp [GlobalsWithin]) executed noGrowth
  have same : ∀ index < after.length, rename index = nextMap index := by
    intro index bounded
    exact (extended.agrees index (by omega)).symm
  have finalLayout := extended.layout.congr same
  have sameIterator := relocateValue_congr rename nextMap after.length iterator same iteratorInside
  have moved := Relocation.iterMethod_runtime_relocates layout.runtime module receiver source inside
  rw [bound] at moved
  simp only [Option.map, Except.map] at moved
  have nextMoved := Relocation.nextMethod_runtime_relocates finalLayout.runtime module iterator source iteratorInside
  rw [valid] at nextMoved
  simp only [Option.map, Except.map] at nextMoved
  have instanceMoved : isInstance physical (relocateValue rename receiver) = true :=
    (Relocation.isInstance_relocates layout.runtime receiver inside).trans isObject
  refine ⟨other, finalLayout, fun address object initial => (kept address object initial).congr same, ?_⟩
  intro loop resumes inputName getInput
  apply Reaches.next (following := .running
    ⟨⟨.expr (.name inputName) loop.env,
      .sequence loop.name loop.body loop.otherwise loop.following loop.env :: loop.stack, physical⟩, used⟩ resumes) rfl
  apply (Reaches.of_heap (Evaluates.lookup getInput anchors _) resumes).trans
  apply Reaches.next (following := .running
    ⟨⟨.operation (relocateRuntimeOperation rename operation) [], [], physical⟩, used⟩ (.acquire loop :: resumes))
  · simp [step, intercept, instanceMoved, enter, moved]
  · apply acquired (operation := relocateRuntimeOperation rename advance) (valid := nextMoved)
    simpa only [relocateCompletion, relocateGlobals, List.map_nil, Except.map, ← sameIterator] using
      called (.acquire loop :: resumes)

end FormalSW.PyAst.IteratorCalls
