import lang.py.FormalSW.MachineExecutionInvariant
import lang.py.FormalSW.ExecutionSimulation

/-! Whole executions correspond across allocations, mutations and suspended iterator calls. -/
namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation
set_option Elab.async false

/-- Allocations may extend the map, while every original object keeps its image. -/
structure ExtendedLayout (logicalSize physicalSize : Nat) (original : Nat → Nat)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) : Prop where
  layout : ExecutionLayout logical physical rename
  logicalGrows : logicalSize ≤ logical.length
  physicalGrows : physicalSize ≤ physical.length
  agrees : ∀ address < logicalSize, rename address = original address

def ExecutionStates (logicalSize physicalSize : Nat) (original : Nat → Nat) (anchors : Nat)
    (globals otherGlobals : Mutable.Globals) (left right : State) : Prop :=
  ∃ logical physical rename, ExtendedLayout logicalSize physicalSize original logical physical rename ∧
    StateHeap logical left ∧ StateWithin logical.length left ∧ GlobalsWithin logical.length globals ∧
    otherGlobals = relocateGlobals rename globals ∧ right = relocateState rename physical anchors left

def ExecutionOutcomes (logicalSize physicalSize : Nat) (original : Nat → Nat) (anchors : Nat)
    (left right : Except ExceptionObject Mutable.Completion) : Prop :=
  ∃ logical physical rename, ExtendedLayout logicalSize physicalSize original logical physical rename ∧
    StepHeap logical (.done left) ∧ StepWithin logical.length (.done left) ∧
    right = left.map (relocateCompletion rename physical anchors)

theorem execution_transition (module : Module) (choices : ChoiceSchedule)
    (logicalSize physicalSize : Nat) (original : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (globals otherGlobals : Mutable.Globals) (source : ModuleSource module) (left right : State)
    (related : ExecutionStates logicalSize physicalSize original physicalAnchors globals otherGlobals left right) :
    Step.Relates (ExecutionStates logicalSize physicalSize original physicalAnchors globals otherGlobals)
      (ExecutionOutcomes logicalSize physicalSize original physicalAnchors)
      (IteratorCalls.step module logicalAnchors choices left globals)
      (IteratorCalls.step module physicalAnchors choices right otherGlobals) := by
  obtain ⟨logical, physical, rename, extension, heap, inside, globalsInside, globalsEqual, rfl⟩ := related
  obtain ⟨after, other, nextMap, agree, grows, physicalGrows, retained, afterHeap, afterInside, paired⟩ :=
    step_complete_preserves module choices left logical physical rename logicalAnchors physicalAnchors globals
      source extension.layout heap inside globalsInside
  have extended : ExtendedLayout logicalSize physicalSize original after other nextMap :=
    ⟨retained, Nat.le_trans extension.logicalGrows grows, Nat.le_trans extension.physicalGrows physicalGrows,
      fun address valid => (agree address (Nat.lt_of_lt_of_le valid extension.logicalGrows)).trans
        (extension.agrees address valid)⟩
  have nextGlobals : otherGlobals = relocateGlobals nextMap globals :=
    globalsEqual.trans (relocateGlobals_congr nextMap rename logical.length globals agree globalsInside).symm
  have same : IteratorCalls.step module physicalAnchors choices
      (relocateState rename physical physicalAnchors left) otherGlobals =
      relocateStep nextMap other physicalAnchors (IteratorCalls.step module logicalAnchors choices left globals) := by
    simpa only [globalsEqual] using paired
  rw [same]
  cases stepped : IteratorCalls.step module logicalAnchors choices left globals with
  | next following =>
    apply Step.Relates.next
    exact ⟨after, other, nextMap, extended, by simpa [stepped] using afterHeap,
      by simpa [stepped] using afterInside, globalsInside.mono grows, nextGlobals, rfl⟩
  | done outcome =>
    apply Step.Relates.done
    exact ⟨after, other, nextMap, extended, by simpa [stepped] using afterHeap,
      by simpa [stepped] using afterInside, rfl⟩
  | unsupported => exact .unsupported

/-- The actual iterator machine, started at an arbitrary saved state. -/
def executionFrom (module : Module) (anchors : Nat) (choices : ChoiceSchedule)
    (state : State) (globals : Mutable.Globals) : Execution Mutable.Completion :=
  ⟨State, state, fun current => IteratorCalls.step module anchors choices current globals⟩

/-- No premise supplies the other execution or assumes that either side terminates. -/
theorem execution_bisimulation (module : Module) (choices : ChoiceSchedule) (state : State)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (heap : StateHeap logical state) (inside : StateWithin logical.length state)
    (globalsInside : GlobalsWithin logical.length globals) :
    Execution.Bisimulation
      (executionFrom module logicalAnchors choices state globals)
      (executionFrom module physicalAnchors choices (relocateState rename physical physicalAnchors state)
        (relocateGlobals rename globals))
      (ExecutionStates logical.length physical.length rename physicalAnchors globals (relocateGlobals rename globals))
      (ExecutionOutcomes logical.length physical.length rename physicalAnchors) := by
  refine ⟨?_, ?_⟩
  · exact ⟨logical, physical, rename, ⟨layout, Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl⟩,
      heap, inside, globalsInside, rfl, rfl⟩
  · intro left right related
    exact execution_transition module choices logical.length physical.length rename logicalAnchors physicalAnchors
      globals (relocateGlobals rename globals) source left right related

theorem call_bisimulation (module : Module) (choices : ChoiceSchedule) (name : String)
    (values : List Mutable.Value) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (inside : ∀ value ∈ values, value.edge.Within logical.length)
    (globalsInside : GlobalsWithin logical.length globals) :
    Execution.Bisimulation
      ((IteratorCalls.call module name values logical globals).run choices).execution
      ((IteratorCalls.call module name (values.map (relocateValue rename)) physical (relocateGlobals rename globals)).run choices).execution
      (ExecutionStates logical.length physical.length rename physical.length globals (relocateGlobals rename globals))
      (ExecutionOutcomes logical.length physical.length rename physical.length) := by
  exact execution_bisimulation module choices (.running ⟨⟨.operation (.call name) values, [], logical⟩, 0⟩ [])
    logical physical rename logical.length physical.length globals source layout rfl
    ⟨⟨trivial, inside⟩, by simp, by simp⟩ globalsInside

/-- A finite protocol prefix transports before its suspended consumer resumes. -/
theorem reaches_relocates (module : Module) (choices : ChoiceSchedule)
    (logicalSize physicalSize : Nat) (original : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (globals otherGlobals : Mutable.Globals) (source : ModuleSource module) (left right final : State)
    (related : ExecutionStates logicalSize physicalSize original physicalAnchors globals otherGlobals left right)
    (reached : Reaches module logicalAnchors choices globals left final) :
    ∃ otherFinal, ExecutionStates logicalSize physicalSize original physicalAnchors globals otherGlobals final otherFinal ∧
      Reaches module physicalAnchors choices otherGlobals right otherFinal := by
  induction reached generalizing right with
  | refl => exact ⟨right, related, .refl⟩
  | next transition _ ih =>
    have paired := execution_transition module choices logicalSize physicalSize original logicalAnchors physicalAnchors
      globals otherGlobals source _ right related
    rw [transition] at paired
    obtain ⟨following, stepped, retained⟩ := paired.next_inv
    obtain ⟨otherFinal, finalRelated, rest⟩ := ih following retained
    exact ⟨otherFinal, finalRelated, .next stepped rest⟩

end FormalSW.PyAst.IteratorCalls.Relocation
