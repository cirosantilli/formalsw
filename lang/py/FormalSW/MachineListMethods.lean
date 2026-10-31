import lang.py.FormalSW.ListMethodRelocation
import lang.py.FormalSW.MachineSliceInvariant

/-! Counting and in-place sorting read the captured list after argument effects. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem result_count_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (address : Nat) (needle : Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (addressInside : address < logical.length)
    (needleInside : needle.edge.Within logical.length) (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (primitive (.count address) [needle]) stack globals)
      (result physicalAnchors physical (primitive (.count (rename address)) [relocateValue rename needle])
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem addressInside
  have moved := layout.runtime.lookup address _ found
  cases object : logical[address] <;> simp only [object, relocateObject] at moved
  case list items =>
    have paired := countElements_relocates logical physical rename layout.runtime needle items needleInside
      (layout.closed (.list items) (List.mem_of_getElem? (found.trans (congrArg some object))))
    cases counted : countElements needle items with
    | none =>
      apply Preserves.unchanged layout <;>
        simp [result, run, primitive, found, object, moved, paired, counted, Mutable.unsupported, StepHeap, StepWithin, relocateStep]
    | some total =>
      have preserved := result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (.ok (.int total))) stack globals layout stackInside globalsInside
      simpa [result, run, primitive, found, object, moved, paired, counted, scalarResult] using preserved
  all_goals
    apply Preserves.unchanged layout <;>
      simp [result, run, primitive, found, object, moved, Mutable.unsupported, StepHeap, StepWithin, relocateStep]

theorem result_sortListCore_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (address : Nat) (reverse : Bool) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (addressInside : address < logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (sortListCore address reverse) stack globals)
      (result physicalAnchors physical (sortListCore (rename address) reverse)
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem addressInside
  have moved := layout.runtime.lookup address _ found
  cases object : logical[address] <;> simp only [object, relocateObject] at moved
  case list items =>
    by_cases allScalars : scalarValues items = true
    · obtain ⟨scalars, rfl⟩ := scalarValues_true items allScalars
      have leftFound := found.trans (congrArg some object)
      simp only [List.map_map, Function.comp_def, relocateValue] at moved
      cases ordered : sortedScalars reverse scalars with
      | error exception =>
        apply Preserves.unchanged layout <;>
          simp [result, run, sortListCore_scalars logical address reverse scalars leftFound,
            sortListCore_scalars physical (rename address) reverse scalars moved, ordered, StepHeap, StepWithin, relocateStep]
      | ok sorted =>
        have bounded : ObjectWithin logical.length (.list (sorted.map Mutable.Value.scalar)) := by
          intro value member
          obtain ⟨scalar, _, rfl⟩ := List.mem_map.mp member
          trivial
        have preserved := result_storeSliceObject_preserves logical physical rename logicalAnchors physicalAnchors
          address (.list (scalars.map Mutable.Value.scalar)) (.list (sorted.map Mutable.Value.scalar)) stack globals layout
          leftFound (by simp) (by simp) bounded stackInside globalsInside
        simpa only [result, run, sortListCore_scalars logical address reverse scalars leftFound,
          sortListCore_scalars physical (rename address) reverse scalars moved, ordered, storeSliceObject,
          relocateObject, List.map_map, Function.comp_def, relocateValue, Mutable.eval_bind, Except.map] using preserved
    · apply Preserves.unchanged layout <;>
        simp [result, run, sortListCore, found, object, moved, scalarValues_relocates, allScalars,
          Mutable.unsupported, StepHeap, StepWithin, relocateStep]
  all_goals
    apply Preserves.unchanged layout <;>
      simp [result, run, sortListCore, found, object, moved, Mutable.unsupported, StepHeap, StepWithin, relocateStep]

theorem result_sort_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (address : Nat) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (addressInside : address < logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (primitive (.sort address) []) stack globals)
      (result physicalAnchors physical (primitive (.sort (rename address)) [])
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  rw [primitive_sort_core, primitive_sort_core]
  exact result_sortListCore_preserves logical physical rename logicalAnchors physicalAnchors address false stack globals layout addressInside stackInside globalsInside

theorem result_sortReverse_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (address : Nat) (reverse : Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (addressInside : address < logical.length)
    (reverseInside : reverse.edge.Within logical.length) (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (primitive (.sortReverse address) [reverse]) stack globals)
      (result physicalAnchors physical (primitive (.sortReverse (rename address)) [relocateValue rename reverse])
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  rw [primitive_sortReverse_core, primitive_sortReverse_core, result_bind, result_bind]
  apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _ id _ _ globals layout globalsInside
    (fun outcome after executed => sortDirection_heap logical after reverse reverseInside outcome executed)
    (by simpa only [Except.map_id] using sortDirection_relocates logical physical rename layout.runtime reverse reverseInside)
  intro flag _
  exact result_sortListCore_preserves logical physical rename logicalAnchors physicalAnchors address flag stack globals layout addressInside stackInside globalsInside

inductive ListMethodOperation : Operation → Prop
  | count (address : Nat) : ListMethodOperation (.count address)
  | sort (address : Nat) : ListMethodOperation (.sort address)
  | sortReverse (address : Nat) : ListMethodOperation (.sortReverse address)

theorem step_listMethod_preserves (module : Module)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (operation : Operation) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (covered : ListMethodOperation operation)
    (inside : StateWithin ⟨.operation operation values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation operation values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation operation values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases covered with
  | count address =>
    rcases values with _ | ⟨needle, _ | ⟨extra, rest⟩⟩
    case cons.nil =>
      exact (result_count_preserves logical physical rename logicalAnchors physicalAnchors address needle stack globals
        layout inside.1.1 (inside.1.2 needle (by simp)) inside.2 globalsInside).protectGenerator stack inside.2
    all_goals
      exact (result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (.error ⟨"TypeError", []⟩)) stack globals layout inside.2 globalsInside).protectGenerator stack inside.2
  | sort address =>
    cases values with
    | nil =>
      exact (result_sort_preserves logical physical rename logicalAnchors physicalAnchors address stack globals
        layout inside.1.1 inside.2 globalsInside).protectGenerator stack inside.2
    | cons value rest =>
      exact (result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (.error ⟨"TypeError", []⟩)) stack globals layout inside.2 globalsInside).protectGenerator stack inside.2
  | sortReverse address =>
    rcases values with _ | ⟨reverse, _ | ⟨extra, rest⟩⟩
    case cons.nil =>
      exact (result_sortReverse_preserves logical physical rename logicalAnchors physicalAnchors address reverse stack globals
        layout inside.1.1 (inside.1.2 reverse (by simp)) inside.2 globalsInside).protectGenerator stack inside.2
    all_goals
      exact (result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (.error ⟨"TypeError", []⟩)) stack globals layout inside.2 globalsInside).protectGenerator stack inside.2

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_listMethod_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (operation : Operation) (values : List Mutable.Value) (stack : List Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (covered : ListMethodOperation operation)
    (inside : StateWithin logical.length (.running ⟨⟨.operation operation values, stack, logical⟩, used⟩ resumes))
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices (.running ⟨⟨.operation operation values, stack, logical⟩, used⟩ resumes) globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.running ⟨⟨.operation operation values, stack, logical⟩, used⟩ resumes))
        (relocateGlobals rename globals)) := by
  apply step_preserves module choices (.running ⟨⟨.operation operation values, stack, logical⟩, used⟩ resumes)
    logical physical rename logicalAnchors physicalAnchors globals source layout rfl inside globalsInside
  intro core pending same _
  cases same
  exact SetCalls.Relocation.step_preserves_of_heap module choices _ physical rename logicalAnchors physicalAnchors
    globals layout ⟨inside.1, inside.2.1⟩ globalsInside
    (HeapCalls.Relocation.step_listMethod_preserves module logical physical rename logicalAnchors physicalAnchors
      operation values stack globals layout covered ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
