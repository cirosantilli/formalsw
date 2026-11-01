import lang.py.FormalSW.SortedBuiltinRelocation
import lang.py.FormalSW.MachineSortCompletion

/-! Ordinary sorting retains argument effects, source representatives and result allocation. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem result_sortedValues_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (reverse : Bool) (items : List Value)
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (itemsInside : ∀ item ∈ items, item.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (sortedValues reverse items) stack globals)
      (result physicalAnchors physical (sortedValues reverse (items.map (relocateValue rename)))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  have paired := layout.runtime.sortWithReverse layout.closed reverse items itemsInside
  cases ordered : HeapSort.sortWithReverse logical reverse items with
  | none =>
    apply Preserves.unchanged layout <;>
      simp [result, run, sortedValues, paired, ordered, Mutable.unsupported, StepHeap, StepWithin, relocateStep]
  | some outcome =>
    cases outcome with
    | error exception =>
      apply Preserves.unchanged layout <;>
        simp [result, run, sortedValues, paired, ordered, StepHeap, StepWithin, relocateStep,
          done, CompletionWithin, globalsInside, Except.map, relocateCompletion]
    | ok sorted =>
      have retained := HeapSort.sortWithReverse_perm logical reverse items sorted ordered
      have bounded : ∀ value ∈ sorted, value.edge.Within logical.length :=
        fun value member => itemsInside value (retained.mem_iff.mp member)
      have allocated := result_allocateList_preserves logical physical rename logicalAnchors physicalAnchors
        sorted stack globals layout bounded stackInside globalsInside
      simpa [sortedValues, paired, ordered, result, run, Mutable.allocate, Except.map] using allocated

theorem result_sortedBuiltin_preserves (hasReverse : Bool) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (valuesInside : ∀ value ∈ values, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (primitive (.builtin (if hasReverse then .sortedReverse else .sorted)) values) stack globals)
      (result physicalAnchors physical
        (primitive (.builtin (if hasReverse then .sortedReverse else .sorted)) (values.map (relocateValue rename)))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  rw [primitive_sorted_eq, primitive_sorted_eq]
  cases hasReverse <;> rcases values with _ | ⟨source, _ | ⟨reverse, _ | ⟨extra, rest⟩⟩⟩
  case false.cons.nil =>
    have bounded := valuesInside source (by simp)
    simp only [sortedPrimitive, List.map_cons, List.map_nil, Bool.false_eq_true, ↓reduceIte, result_bind]
    apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _ (List.map (relocateValue rename))
      _ _ globals layout globalsInside
      (fun outcome after executed => sortedPool_heap logical after source bounded outcome executed)
      (sortedPool_relocates logical physical rename layout.runtime source bounded)
    intro items acquired
    exact result_sortedValues_preserves logical physical rename logicalAnchors physicalAnchors false items stack globals
      layout (sortedPool_bounded logical logical layout.closed source items acquired) stackInside globalsInside
  case true.cons.cons.nil =>
    have sourceInside := valuesInside source (by simp)
    have reverseInside := valuesInside reverse (by simp)
    simp only [sortedPrimitive, List.map_cons, List.map_nil, ↓reduceIte, result_bind]
    apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _ (List.map (relocateValue rename))
      _ _ globals layout globalsInside
      (fun outcome after executed => sortedPool_heap logical after source sourceInside outcome executed)
      (sortedPool_relocates logical physical rename layout.runtime source sourceInside)
    intro items acquired
    apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _ id _ _ globals layout globalsInside
      (fun outcome after executed => sortDirection_heap logical after reverse reverseInside outcome executed)
      (by simpa only [Except.map_id] using sortDirection_relocates logical physical rename layout.runtime reverse reverseInside)
    intro direction _
    exact result_sortedValues_preserves logical physical rename logicalAnchors physicalAnchors direction items stack globals
      layout (sortedPool_bounded logical logical layout.closed source items acquired) stackInside globalsInside
  all_goals
    apply Preserves.unchanged layout <;>
      simp [sortedPrimitive, result, run, Mutable.error, Mutable.unsupported, StepHeap, StepWithin,
        done, CompletionWithin, globalsInside, relocateStep, relocateCompletion, Except.map]

theorem step_sortedBuiltin_preserves (module : Module) (hasReverse : Bool)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.operation (.builtin (if hasReverse then .sortedReverse else .sorted)) values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation (.builtin (if hasReverse then .sortedReverse else .sorted)) values, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.operation (.builtin (if hasReverse then .sortedReverse else .sorted)) values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  have raw := result_sortedBuiltin_preserves hasReverse logical physical rename logicalAnchors physicalAnchors values stack globals
    layout inside.1.2 inside.2 globalsInside
  cases hasReverse <;> exact raw.protectGenerator stack inside.2

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_sortedBuiltin_preserves (module : Module) (hasReverse : Bool) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (values : List Mutable.Value) (stack : List HeapCalls.Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin logical.length (.running
      ⟨⟨.operation (.builtin (if hasReverse then .sortedReverse else .sorted)) values, stack, logical⟩, used⟩ resumes))
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices (.running
        ⟨⟨.operation (.builtin (if hasReverse then .sortedReverse else .sorted)) values, stack, logical⟩, used⟩ resumes) globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.running
          ⟨⟨.operation (.builtin (if hasReverse then .sortedReverse else .sorted)) values, stack, logical⟩, used⟩ resumes))
        (relocateGlobals rename globals)) := by
  apply step_preserves module choices (.running
      ⟨⟨.operation (.builtin (if hasReverse then .sortedReverse else .sorted)) values, stack, logical⟩, used⟩ resumes)
    logical physical rename logicalAnchors physicalAnchors globals source layout rfl inside globalsInside
  intro core pending same _
  cases same
  exact SetCalls.Relocation.step_preserves_of_heap module choices _ physical rename logicalAnchors physicalAnchors
    globals layout ⟨inside.1, inside.2.1⟩ globalsInside
    (HeapCalls.Relocation.step_sortedBuiltin_preserves module hasReverse logical physical rename logicalAnchors physicalAnchors
      values stack globals layout ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
