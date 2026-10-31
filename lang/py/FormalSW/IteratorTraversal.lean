import lang.py.FormalSW.IteratorExecutionIsolation

/-! Finite traversals consist of actual next-method executions, including their effects and choice positions. -/
namespace FormalSW.PyAst.Mutable.Relocation

theorem PrivateLayout.congr {logical physical : Heap} {left right : Nat → Nat}
    {address : Nat} {object : Object} (layout : PrivateLayout logical physical left address object)
    (agree : ∀ index < logical.length, right index = left index) :
    PrivateLayout logical physical right address object := by
  refine ⟨layout.layout.congr agree, layout.saved, ?_⟩
  intro index inside
  rw [agree index inside]
  exact layout.excludes index inside

end FormalSW.PyAst.Mutable.Relocation

namespace FormalSW.PyAst.IteratorCalls
open HeapCalls HeapCalls.Relocation Mutable.Relocation
set_option Elab.async false

def NextRun (module : Module) (choices : ChoiceSchedule) (iterator : Mutable.Value)
    (before : Mutable.Heap) (used : Nat) (outcome : Except ExceptionObject Mutable.Value)
    (after : Mutable.Heap) (finalUsed : Nat) : Prop :=
  ∃ operation, iterator.edge.Within before.length ∧ isInstance before iterator = true ∧
    ProtocolCalls.nextMethod module iterator before = some (.ok (some operation), before) ∧
    Reaches module before.length choices []
      (.running ⟨⟨.operation operation [], [], before⟩, used⟩ [])
      (.completed (.ok ⟨outcome, [], after, before.length⟩) finalUsed [])

/-- The trace admits allocation; heap-size restrictions belong to individual transport theorems. -/
inductive Traversal {α : Type} (module : Module) (choices : ChoiceSchedule)
    (iterator : Mutable.Value) (encode : α → Mutable.Value) :
    Mutable.Heap → Nat → List α → Except ExceptionObject Unit → Mutable.Heap → Nat → Prop
  | exhausted {before after used finalUsed args}
      (ran : NextRun module choices iterator before used (.error ⟨"StopIteration", args⟩) after finalUsed) :
      Traversal module choices iterator encode before used [] (.ok ()) after finalUsed
  | failed {before after used finalUsed error}
      (ran : NextRun module choices iterator before used (.error error) after finalUsed)
      (notExhausted : error.typeName ≠ "StopIteration") :
      Traversal module choices iterator encode before used [] (.error error) after finalUsed
  | yielded {before middle after used nextUsed finalUsed value values outcome}
      (ran : NextRun module choices iterator before used (.ok (encode value)) middle nextUsed)
      (rest : Traversal module choices iterator encode middle nextUsed values outcome after finalUsed) :
      Traversal module choices iterator encode before used (value :: values) outcome after finalUsed

theorem NextRun.effects {module : Module} {choices : ChoiceSchedule} {iterator : Mutable.Value}
    {before after : Mutable.Heap} {used finalUsed : Nat} {outcome : Except ExceptionObject Mutable.Value}
    (ran : NextRun module choices iterator before used outcome after finalUsed)
    (source : Relocation.ModuleSource module) (closed : Closed before) :
    Closed after ∧ before.length ≤ after.length := by
  obtain ⟨operation, inside, _, bound, executed⟩ := ran
  have method := Relocation.nextMethod_source module iterator before before operation source bound
  obtain ⟨finalHeap, _, _, _, grows, _, finalLayout, finalStateHeap, _⟩ :=
    Relocation.reaches_isolated module choices before.length before.length [] source executed before before id
      (ExecutionLayout.refl before closed) rfl
      ⟨⟨method.within before.length inside, by simp⟩, by simp, by simp⟩ (by simp [GlobalsWithin])
  have equal : after = finalHeap := finalStateHeap
  subst finalHeap
  exact ⟨finalLayout.closed, grows⟩

theorem Traversal.effects {α : Type} {module : Module} {choices : ChoiceSchedule} {iterator : Mutable.Value}
    {encode : α → Mutable.Value} {before after : Mutable.Heap} {used finalUsed : Nat}
    {values : List α} {outcome : Except ExceptionObject Unit}
    (trace : Traversal module choices iterator encode before used values outcome after finalUsed)
    (source : Relocation.ModuleSource module) (closed : Closed before) :
    Closed after ∧ before.length ≤ after.length := by
  induction trace with
  | exhausted ran => exact ran.effects source closed
  | failed ran _ => exact ran.effects source closed
  | yielded ran _ ih =>
      obtain ⟨middleClosed, grows⟩ := ran.effects source closed
      obtain ⟨afterClosed, later⟩ := ih middleClosed
      exact ⟨afterClosed, Nat.le_trans grows later⟩

def exitOutcome (error : ExceptionObject) : Except ExceptionObject Unit :=
  if error.typeName = "StopIteration" then .ok () else .error error

/-- Exhaustion resumes the source loop; any other exception propagates its exact payload. -/
def ExitResult (module : Module) (choices : ChoiceSchedule) (anchors : Nat) (first : State)
    (loop : Loop) (resumes : List Resume) (after : Mutable.Heap) (used : Nat) :
    Except ExceptionObject Unit → Prop
  | .ok () => Reaches module anchors choices [] first
      (.running ⟨⟨.block (loop.otherwise ++ loop.following) loop.env, loop.stack, after⟩, used⟩ resumes)
  | .error error => Reaches module anchors choices [] first
      (.completed (.ok ⟨.error error, [], after, anchors⟩) used resumes)

theorem ExitResult.before {module : Module} {choices : ChoiceSchedule} {anchors : Nat}
    {first middle : State} {loop : Loop} {resumes : List Resume} {after : Mutable.Heap} {used : Nat}
    {outcome : Except ExceptionObject Unit} (entered : Reaches module anchors choices [] first middle)
    (exited : ExitResult module choices anchors middle loop resumes after used outcome) :
    ExitResult module choices anchors first loop resumes after used outcome := by
  cases outcome with
  | error error => exact entered.trans exited
  | ok value => cases value; exact entered.trans exited

theorem NextRun.exit_isolated {module : Module} {choices : ChoiceSchedule} {iterator : Mutable.Value}
    {before after : Mutable.Heap} {used finalUsed : Nat} {error : ExceptionObject}
    (ran : NextRun module choices iterator before used (.error error) after finalUsed)
    (source : Relocation.ModuleSource module) (physical : Mutable.Heap) (rename : Nat → Nat)
    (layout : ExecutionLayout before physical rename) (noGrowth : after.length = before.length) (anchors : Nat) :
    ∃ other, ExecutionLayout after other rename ∧
      (∀ address object, PrivateLayout before physical rename address object →
        PrivateLayout after other rename address object) ∧
      ∀ loop resumes, ExitResult module choices anchors
        (.running ⟨⟨.block (loopCode loop (relocateValue rename iterator) :: loop.following) loop.env,
          loop.stack, physical⟩, used⟩ resumes)
        loop resumes other finalUsed (exitOutcome error) := by
  obtain ⟨operation, inside, isObject, bound, executed⟩ := ran
  obtain ⟨other, nextMap, extended, kept, called⟩ := Relocation.advance_completion_isolated
    module choices before physical rename before.length anchors used finalUsed iterator operation
    (.error error) after [] source layout inside (by simp [GlobalsWithin]) isObject bound executed noGrowth
  have same : ∀ index < after.length, rename index = nextMap index := by
    intro index bounded
    exact (extended.agrees index (by omega)).symm
  refine ⟨other, extended.layout.congr same, fun address object initial =>
    (kept address object initial).congr same, ?_⟩
  intro loop resumes
  have completion : Reaches module anchors choices []
      (.running ⟨⟨.block (loopCode loop (relocateValue rename iterator) :: loop.following) loop.env,
        loop.stack, physical⟩, used⟩ resumes)
      (.completed (.ok ⟨.error error, [], other, anchors⟩) finalUsed
        (.advance loop (relocateValue rename iterator) :: resumes)) := by
    simpa only [relocateGlobals, List.map_nil, Except.map] using called loop resumes
  by_cases stopped : error.typeName = "StopIteration"
  · rw [exitOutcome, if_pos stopped]
    rcases error with ⟨name, args⟩
    change name = "StopIteration" at stopped
    subst name
    exact exhausted completion
  · rw [exitOutcome, if_neg stopped]
    apply completion.trans
    exact .next (by simp [step, resume, stopped, propagate, Calls.generatorException]) .refl

end FormalSW.PyAst.IteratorCalls
