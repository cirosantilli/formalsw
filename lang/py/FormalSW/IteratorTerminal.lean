import lang.py.FormalSW.IteratorPrefix

/-! A final iterator call may allocate before raising or yielding a value rejected by its consumer. -/
namespace FormalSW.PyAst.IteratorCalls
open HeapCalls HeapCalls.Relocation Mutable.Relocation
set_option Elab.async false

/-- Ordinary iteration errors propagate with all caller effects; StopIteration needs the exhaustion rule. -/
theorem NextRun.failure_relocates {module : Module} {choices : ChoiceSchedule} {iterator : Mutable.Value}
    {before after : Mutable.Heap} {used finalUsed : Nat} {error : ExceptionObject}
    (ran : NextRun module choices iterator before used (.error error) after finalUsed)
    (notExhausted : error.typeName ≠ "StopIteration")
    (source : Relocation.ModuleSource module) (physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout before physical rename) (anchors : Nat) :
    ∃ other nextMap, Relocation.ExtendedLayout before.length physical.length rename after other nextMap ∧
      ∀ (loop : Loop) (resumes : List Resume), Reaches module anchors choices []
        (.running ⟨⟨.block (loopCode loop (relocateValue rename iterator) :: loop.following) loop.env,
          loop.stack, physical⟩, used⟩ resumes)
        (.completed (.ok ⟨.error error, [], other, anchors⟩) finalUsed resumes) := by
  obtain ⟨operation, inside, isObject, bound, executed⟩ := ran
  obtain ⟨other, nextMap, extended, called⟩ := Relocation.advance_completion_relocates
    module choices before physical rename before.length anchors used finalUsed iterator operation
    (.error error) after [] source layout inside (by simp [GlobalsWithin]) isObject bound executed
  refine ⟨other, nextMap, extended, ?_⟩
  intro loop resumes
  apply (show Reaches module anchors choices [] _ _ from by
    simpa only [relocateGlobals, List.map_nil, Except.map] using called loop resumes).trans
  exact .next (by simp [step, resume, propagate, notExhausted, Calls.generatorException]) .refl

/-- Scalar yields can resume validation with a final runtime layout even when the method allocated. -/
theorem NextRun.scalar_relocates {module : Module} {choices : ChoiceSchedule} {iterator : Mutable.Value}
    {before after : Mutable.Heap} {used finalUsed : Nat} {value : Constant}
    (ran : NextRun module choices iterator before used (.ok (.scalar value)) after finalUsed)
    (source : Relocation.ModuleSource module) (physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout before physical rename) (anchors : Nat) :
    ∃ other nextMap, Relocation.ExtendedLayout before.length physical.length rename after other nextMap ∧
      ∀ (loop : Loop) (resumes : List Resume), Reaches module anchors choices []
        (.running ⟨⟨.block (loopCode loop (relocateValue rename iterator) :: loop.following) loop.env,
          loop.stack, physical⟩, used⟩ resumes)
        (.running ⟨⟨.block (loop.body ++ [Calls.loopContinuation loop.body (loopCode loop (relocateValue rename iterator))]
          ++ loop.following) (setLocal loop.env loop.name (.scalar value)),
          loop.stack, other⟩, finalUsed⟩ resumes) := by
  obtain ⟨operation, inside, isObject, bound, executed⟩ := ran
  obtain ⟨other, nextMap, extended, called⟩ := Relocation.advance_completion_relocates
    module choices before physical rename before.length anchors used finalUsed iterator operation
    (.ok (.scalar value)) after [] source layout inside (by simp [GlobalsWithin]) isObject bound executed
  refine ⟨other, nextMap, extended, ?_⟩
  intro loop resumes
  apply advanced
  simpa only [relocateGlobals, List.map_nil, Except.map, relocateValue] using called loop resumes

end FormalSW.PyAst.IteratorCalls
