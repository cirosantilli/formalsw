import lang.py.FormalSW.IteratorAllocatingIsolation
import lang.py.FormalSW.IteratorPrefix

namespace FormalSW.PyAst.IteratorCalls
open HeapCalls HeapCalls.Relocation Mutable.Relocation
set_option Elab.async false

/-- A next-method execution certified by stable segments and supported allocation steps. -/
def AllocatingNextRun (module : Module) (choices : ChoiceSchedule) (iterator : Mutable.Value)
    (before : Mutable.Heap) (used : Nat) (outcome : Except ExceptionObject Mutable.Value)
    (after : Mutable.Heap) (finalUsed : Nat) : Prop :=
  ∃ operation, iterator.edge.Within before.length ∧ isInstance before iterator = true ∧
    ProtocolCalls.nextMethod module iterator before = some (.ok (some operation), before) ∧
    AllocatingTrace module before.length choices [] before
      (.running ⟨⟨.operation operation [], [], before⟩, used⟩ []) after
      (.completed (.ok ⟨outcome, [], after, before.length⟩) finalUsed [])

theorem AllocatingNextRun.nextRun {module : Module} {choices : ChoiceSchedule} {iterator : Mutable.Value}
    {before after : Mutable.Heap} {used finalUsed : Nat} {outcome : Except ExceptionObject Mutable.Value}
    (ran : AllocatingNextRun module choices iterator before used outcome after finalUsed) :
    NextRun module choices iterator before used outcome after finalUsed := by
  obtain ⟨operation, inside, isObject, bound, executed⟩ := ran
  exact ⟨operation, inside, isObject, bound, executed.reaches⟩

theorem NextRun.allocating_of_noGrowth {module : Module} {choices : ChoiceSchedule} {iterator : Mutable.Value}
    {before after : Mutable.Heap} {used finalUsed : Nat} {outcome : Except ExceptionObject Mutable.Value}
    (ran : NextRun module choices iterator before used outcome after finalUsed)
    (noGrowth : after.length = before.length) :
    AllocatingNextRun module choices iterator before used outcome after finalUsed := by
  obtain ⟨operation, inside, isObject, bound, executed⟩ := ran
  exact ⟨operation, inside, isObject, bound, .stable rfl rfl noGrowth executed⟩

theorem AllocatingNextRun.advance_isolated {module : Module} {choices : ChoiceSchedule} {iterator : Mutable.Value}
    {before after : Mutable.Heap} {used finalUsed : Nat} {outcome : Except ExceptionObject Mutable.Value}
    (ran : AllocatingNextRun module choices iterator before used outcome after finalUsed)
    (source : Relocation.ModuleSource module) (physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout before physical rename) (anchors : Nat) :
    ∃ other nextMap, Relocation.ExtendedLayout before.length physical.length rename after other nextMap ∧
      (∀ address object, object ≠ .tuple [] → PrivateLayout before physical rename address object →
        PrivateLayout after other nextMap address object) ∧
      ∀ loop resumes, Reaches module anchors choices []
        (.running ⟨⟨.block (loopCode loop (relocateValue rename iterator) :: loop.following) loop.env,
          loop.stack, physical⟩, used⟩ resumes)
        (.completed (.ok ⟨outcome.map (relocateValue nextMap), [], other, anchors⟩)
          finalUsed (.advance loop (relocateValue rename iterator) :: resumes)) := by
  obtain ⟨operation, inside, isObject, bound, executed⟩ := ran
  have method := Relocation.nextMethod_source module iterator before before operation source bound
  obtain ⟨other, nextMap, extended, _, kept, called⟩ := executed.isolated source physical rename anchors layout
    ⟨⟨method.within before.length inside, by simp⟩, by simp, by simp⟩ (by simp [GlobalsWithin])
  have moved := Relocation.nextMethod_runtime_relocates layout.runtime module iterator source inside
  rw [bound] at moved
  simp only [Option.map, Except.map] at moved
  have instanceMoved : isInstance physical (relocateValue rename iterator) = true :=
    (Relocation.isInstance_relocates layout.runtime iterator inside).trans isObject
  refine ⟨other, nextMap, extended, kept, fun loop resumes => ?_⟩
  apply Reaches.next (following := .running
    ⟨⟨.operation (relocateRuntimeOperation rename operation) [], [], physical⟩, used⟩
      (.advance loop (relocateValue rename iterator) :: resumes))
  · simp [step, intercept, loopCode, instanceMoved, enter, moved]
  · simpa only [Relocation.relocateState, Relocation.relocateCore, HeapCalls.Relocation.relocateState,
      relocateWork, List.map_nil, Except.map, relocateCompletion, relocateGlobals, appendResumes, List.nil_append] using
      called.append_resumes (.advance loop (relocateValue rename iterator) :: resumes)

theorem AllocatingNextRun.scalar_isolated {module : Module} {choices : ChoiceSchedule} {iterator : Mutable.Value}
    {before after : Mutable.Heap} {used finalUsed : Nat} {value : Constant}
    (ran : AllocatingNextRun module choices iterator before used (.ok (.scalar value)) after finalUsed)
    (source : Relocation.ModuleSource module) (physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout before physical rename) (anchors : Nat) :
    ∃ other nextMap, Relocation.ExtendedLayout before.length physical.length rename after other nextMap ∧
      (∀ address object, object ≠ .tuple [] → PrivateLayout before physical rename address object →
        PrivateLayout after other nextMap address object) ∧
      ∀ loop resumes, Reaches module anchors choices []
        (.running ⟨⟨.block (loopCode loop (relocateValue rename iterator) :: loop.following) loop.env,
          loop.stack, physical⟩, used⟩ resumes)
        (.running ⟨⟨.block (loop.body ++ [Calls.loopContinuation loop.body (loopCode loop (relocateValue rename iterator))]
          ++ loop.following) (setLocal loop.env loop.name (.scalar value)),
          loop.stack, other⟩, finalUsed⟩ resumes) := by
  obtain ⟨other, nextMap, extended, kept, called⟩ := ran.advance_isolated source physical rename layout anchors
  refine ⟨other, nextMap, extended, kept, fun loop resumes => ?_⟩
  apply advanced
  simpa only [Except.map, relocateValue] using called loop resumes

theorem AllocatingNextRun.exit_isolated {module : Module} {choices : ChoiceSchedule} {iterator : Mutable.Value}
    {before after : Mutable.Heap} {used finalUsed : Nat} {error : ExceptionObject}
    (ran : AllocatingNextRun module choices iterator before used (.error error) after finalUsed)
    (source : Relocation.ModuleSource module) (physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout before physical rename) (anchors : Nat) :
    ∃ other nextMap, Relocation.ExtendedLayout before.length physical.length rename after other nextMap ∧
      (∀ address object, object ≠ .tuple [] → PrivateLayout before physical rename address object →
        PrivateLayout after other nextMap address object) ∧
      ∀ loop resumes, ExitResult module choices anchors
        (.running ⟨⟨.block (loopCode loop (relocateValue rename iterator) :: loop.following) loop.env,
          loop.stack, physical⟩, used⟩ resumes)
        loop resumes other finalUsed (exitOutcome error) := by
  obtain ⟨other, nextMap, extended, kept, called⟩ := ran.advance_isolated source physical rename layout anchors
  refine ⟨other, nextMap, extended, kept, fun loop resumes => ?_⟩
  have completion := called loop resumes
  simp only [Except.map] at completion
  by_cases stopped : error.typeName = "StopIteration"
  · rw [exitOutcome, if_pos stopped]
    rcases error with ⟨name, args⟩
    change name = "StopIteration" at stopped
    subst name
    exact exhausted completion
  · rw [exitOutcome, if_neg stopped]
    exact completion.trans (.next (by simp [step, resume, stopped, propagate, Calls.generatorException]) .refl)

/-- Finite accepted prefixes may allocate on every call. -/
inductive AllocatingYieldPrefix {α : Type} (module : Module) (choices : ChoiceSchedule)
    (iterator : Mutable.Value) (encode : α → Mutable.Value) :
    Mutable.Heap → Nat → List α → Mutable.Heap → Nat → Prop where
  | nil {heap used} : AllocatingYieldPrefix module choices iterator encode heap used [] heap used
  | cons {before middle after used nextUsed finalUsed value values}
      (ran : AllocatingNextRun module choices iterator before used (.ok (encode value)) middle nextUsed)
      (rest : AllocatingYieldPrefix module choices iterator encode middle nextUsed values after finalUsed) :
      AllocatingYieldPrefix module choices iterator encode before used (value :: values) after finalUsed

theorem AllocatingYieldPrefix.yieldPrefix {α : Type} {module : Module} {choices : ChoiceSchedule}
    {iterator : Mutable.Value} {encode : α → Mutable.Value} {before after : Mutable.Heap}
    {used finalUsed : Nat} {values : List α}
    (trace : AllocatingYieldPrefix module choices iterator encode before used values after finalUsed) :
    YieldPrefix module choices iterator encode before used values after finalUsed := by
  induction trace with
  | nil => exact .nil
  | cons ran _ ih => exact .cons ran.nextRun ih

end FormalSW.PyAst.IteratorCalls
