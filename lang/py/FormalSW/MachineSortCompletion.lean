import lang.py.FormalSW.SortingRelocation
import lang.py.FormalSW.MachineSortAcquisition
import lang.py.FormalSW.MachineSequenceConstruction

/-! Sorting finishes in the heap left by key callbacks, allocating only after success. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem result_sortedFinish_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (reverse : Bool) (keys : List (Value × Value))
    (stack : List Frame) (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (keysInside : ∀ pair ∈ keys, PairWithin logical.length pair)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (sortedFinish reverse keys) stack globals)
      (result physicalAnchors physical (sortedFinish reverse (keys.map (relocatePair rename)))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  have bounded : ∀ pair ∈ keys.reverse, PairWithin logical.length pair :=
    fun pair member => keysInside pair (List.mem_reverse.mp member)
  have paired := layout.runtime.keyedSortWithReverse layout.closed reverse keys.reverse bounded
  change HeapSort.keyedSortWithReverse physical reverse (keys.reverse.map (relocatePair rename)) =
    (HeapSort.keyedSortWithReverse logical reverse keys.reverse).map
      (Except.map (List.map (relocatePair rename))) at paired
  rw [List.map_reverse] at paired
  cases ordered : HeapSort.keyedSortWithReverse logical reverse keys.reverse with
  | none =>
    apply Preserves.unchanged layout <;>
      simp [result, run, sortedFinish, paired, ordered, Mutable.unsupported, StepHeap, StepWithin, relocateStep]
  | some outcome =>
    cases outcome with
    | error exception =>
      apply Preserves.unchanged layout <;>
        simp [result, run, sortedFinish, paired, ordered, StepHeap, StepWithin, relocateStep,
          done, CompletionWithin, globalsInside, Except.map, relocateCompletion]
    | ok sorted =>
      have retained := HeapSort.keyedSortWithReverse_perm logical reverse keys.reverse sorted ordered
      have inside : ∀ value ∈ sorted.map Prod.fst, value.edge.Within logical.length := by
        intro value member
        obtain ⟨pair, present, rfl⟩ := List.mem_map.mp member
        exact (bounded pair (retained.mem_iff.mp present)).1
      have allocated := result_allocateList_preserves logical physical rename logicalAnchors physicalAnchors
        (sorted.map Prod.fst) stack globals layout inside stackInside globalsInside
      simpa [sortedFinish, paired, ordered, result, run, Mutable.allocate, Except.map,
        List.map_map, Function.comp_def, relocatePair] using allocated

theorem step_sortedLoop_preserves (module : Module) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (cursor : SequenceSort) (remaining : List Value)
    (keys : List (Value × Value)) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin ⟨.sortedLoop cursor remaining keys, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.sortedLoop cursor remaining keys, stack, logical⟩ globals)
      (step module physicalAnchors
        (relocateState rename physical ⟨.sortedLoop cursor remaining keys, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases remaining with
  | cons candidate rest =>
    exact step_sorted_key_entry_preserves module logical physical rename logicalAnchors physicalAnchors
      cursor candidate rest keys stack globals layout inside
  | nil =>
    simpa only [step, relocateState, relocateWork, List.map_nil, relocateSort] using
      (result_sortedFinish_preserves logical physical rename logicalAnchors physicalAnchors cursor.reverse keys
        stack globals layout inside.1.2.2 inside.2 globalsInside).protectGenerator stack inside.2

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_sortedLoop_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (cursor : SequenceSort) (remaining : List Mutable.Value) (keys : List (Mutable.Value × Mutable.Value))
    (stack : List HeapCalls.Frame) (resumes : List Resume) (globals : Mutable.Globals)
    (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (inside : StateWithin logical.length (.running ⟨⟨.sortedLoop cursor remaining keys, stack, logical⟩, used⟩ resumes))
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (IteratorCalls.step module logicalAnchors choices (.running ⟨⟨.sortedLoop cursor remaining keys, stack, logical⟩, used⟩ resumes) globals)
      (IteratorCalls.step module physicalAnchors choices
        (relocateState rename physical physicalAnchors (.running ⟨⟨.sortedLoop cursor remaining keys, stack, logical⟩, used⟩ resumes))
        (relocateGlobals rename globals)) := by
  apply step_preserves module choices (.running ⟨⟨.sortedLoop cursor remaining keys, stack, logical⟩, used⟩ resumes)
    logical physical rename logicalAnchors physicalAnchors globals source layout rfl inside globalsInside
  intro core pending same _
  cases same
  exact SetCalls.Relocation.step_preserves_of_heap module choices _ physical rename logicalAnchors physicalAnchors
    globals layout ⟨inside.1, inside.2.1⟩ globalsInside
    (HeapCalls.Relocation.step_sortedLoop_preserves module logical physical rename logicalAnchors physicalAnchors
      cursor remaining keys stack globals layout ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
