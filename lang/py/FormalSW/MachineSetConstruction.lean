import lang.py.FormalSW.SetConstructionEffects
import lang.py.FormalSW.MachineDictionaryMethods

/-! Set construction and insertion retain representatives, partial allocations and caller aliases. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem result_addItem_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (address : Nat) (value : Value) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (addressInside : address < logical.length) (valueInside : value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (Mutable.addItem address value) stack globals)
      (result physicalAnchors physical (Mutable.addItem (rename address) (relocateValue rename value))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  cases executed : Mutable.addItem address value logical with
  | none =>
    have other := (layout.runtime.addItem_unsupported layout.closed address value addressInside valueInside).mpr executed
    apply Preserves.unchanged layout <;> simp [result, run, executed, other, StepHeap, StepWithin, relocateStep]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    obtain ⟨other, paired, retained, sameLength, bounded⟩ := layout.addItem address value addressInside valueInside outcome after executed
    exact result_preserves logical physical after other rename rename logicalAnchors physicalAnchors _ _ stack globals outcome
      (fun _ _ => rfl) (Nat.le_of_eq sameLength.symm) (HeapGrows.addItem _ _ physical _ other paired)
      retained stackInside globalsInside bounded executed paired

theorem result_allocateSetValues_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (items : List Value) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (itemsInside : ∀ value ∈ items, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (Mutable.allocateSetValues items) stack globals)
      (result physicalAnchors physical (Mutable.allocateSetValues (items.map (relocateValue rename)))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  cases executed : Mutable.allocateSetValues items logical with
  | none =>
    have other := (layout.allocateSetValues_unsupported items itemsInside).mpr executed
    apply Preserves.unchanged layout <;> simp [result, run, executed, other, StepHeap, StepWithin, relocateStep]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    obtain ⟨other, paired, retained, sameLength, bounded⟩ := layout.allocateSetValues items itemsInside outcome after executed
    exact result_preserves logical physical after other rename (extendMap rename logical.length physical.length)
      logicalAnchors physicalAnchors _ _ stack globals outcome (extendMap_old _ _ _)
      (by omega) (HeapGrows.allocateSetValues _ physical _ other paired) retained stackInside globalsInside bounded executed paired

theorem result_setFrom_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (source : Value) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (sourceInside : source.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (Mutable.setFrom source) stack globals)
      (result physicalAnchors physical (Mutable.setFrom (relocateValue rename source))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  rw [setFrom_eq, setFrom_eq, result_bind, result_bind]
  apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _ (List.map (relocateValue rename))
    _ _ globals layout globalsInside
    (fun outcome after executed => setSourceItems_keeps_heap logical after source sourceInside outcome executed)
    (layout.runtime.setSourceItems source sourceInside)
  intro items read
  exact result_allocateSetValues_preserves logical physical rename logicalAnchors physicalAnchors items stack globals layout
    (setSourceItems_bounded logical layout.closed source sourceInside items read) stackInside globalsInside

inductive SetConstructionOperation : Operation → Prop
  | add (address : Nat) : SetConstructionOperation (.add address)
  | display : SetConstructionOperation (.builtin .setDisplay)
  | constructor : SetConstructionOperation (.builtin .set)

theorem step_setConstruction_preserves (module : Module)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (operation : Operation) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (covered : SetConstructionOperation operation)
    (inside : StateWithin ⟨.operation operation values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation operation values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation operation values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases covered with
  | add address =>
    rcases values with _ | ⟨value, _ | ⟨extra, rest⟩⟩
    case cons.nil =>
      exact (result_addItem_preserves logical physical rename logicalAnchors physicalAnchors address value stack globals
        layout inside.1.1 (inside.1.2 value (by simp)) inside.2 globalsInside).protectGenerator stack inside.2
    all_goals exact (result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
      (some (.error ⟨"TypeError", []⟩)) stack globals layout inside.2 globalsInside).protectGenerator stack inside.2
  | display =>
    exact (result_allocateSetValues_preserves logical physical rename logicalAnchors physicalAnchors values stack globals
      layout inside.1.2 inside.2 globalsInside).protectGenerator stack inside.2
  | constructor =>
    rcases values with _ | ⟨source, _ | ⟨extra, rest⟩⟩
    case nil =>
      exact (result_allocateSetValues_preserves logical physical rename logicalAnchors physicalAnchors [] stack globals
        layout (by simp) inside.2 globalsInside).protectGenerator stack inside.2
    case cons.nil =>
      exact (result_setFrom_preserves logical physical rename logicalAnchors physicalAnchors source stack globals
        layout (inside.1.2 source (by simp)) inside.2 globalsInside).protectGenerator stack inside.2
    case cons.cons =>
      exact (result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (.error ⟨"TypeError", []⟩)) stack globals layout inside.2 globalsInside).protectGenerator stack inside.2

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_setConstruction_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (operation : Operation) (values : List Mutable.Value) (stack : List Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (covered : SetConstructionOperation operation)
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
    (HeapCalls.Relocation.step_setConstruction_preserves module logical physical rename logicalAnchors physicalAnchors
      operation values stack globals layout covered ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
