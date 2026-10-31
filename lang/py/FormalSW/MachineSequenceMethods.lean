import lang.py.FormalSW.SequenceMethodRelocation
import lang.py.FormalSW.MachineDictionaryMethods

/-! Append and pop preserve live mutations through saved callers and iterator consumers. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem result_appendItem_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (address : Nat) (value : Value) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (addressInside : address < logical.length) (valueInside : value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (Mutable.appendItem address value) stack globals)
      (result physicalAnchors physical (Mutable.appendItem (rename address) (relocateValue rename value))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  obtain ⟨outcome, after, other, left, right, retained, logicalSize, physicalSize, bounded⟩ :=
    layout.appendItem address value addressInside valueInside
  exact result_preserves logical physical after other rename rename logicalAnchors physicalAnchors _ _ stack globals outcome
    (fun _ _ => rfl) (Nat.le_of_eq logicalSize.symm) (Nat.le_of_eq physicalSize.symm) retained stackInside globalsInside bounded left right

theorem result_popItem_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (address : Nat) (subscript : Value) (stack : List Frame)
    (globals : Mutable.Globals) (layout : ExecutionLayout logical physical rename)
    (addressInside : address < logical.length) (indexInside : subscript.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (Mutable.popItem address subscript) stack globals)
      (result physicalAnchors physical (Mutable.popItem (rename address) (relocateValue rename subscript))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  have normalized (address : Nat) (subscript : Value) : Mutable.popItem address subscript =
      (do let position ← popIndex subscript; Mutable.popItem address (.scalar (.int position))) :=
    funext (fun heap => popItem_index heap address subscript)
  rw [normalized, normalized, result_bind, result_bind]
  apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _ id _ _ globals layout globalsInside
    (fun outcome after executed => popIndex_heap logical after subscript outcome executed)
    (by simpa only [Except.map_id] using layout.runtime.popIndex_relocates subscript indexInside)
  intro position _
  obtain ⟨outcome, after, other, left, right, retained, logicalSize, physicalSize, bounded⟩ :=
    layout.popItem_integer address position addressInside
  exact result_preserves logical physical after other rename rename logicalAnchors physicalAnchors _ _ stack globals outcome
    (fun _ _ => rfl) (Nat.le_of_eq logicalSize.symm) (Nat.le_of_eq physicalSize.symm) retained stackInside globalsInside bounded left right

inductive SequenceMutationOperation : Operation → Prop
  | append (address : Nat) : SequenceMutationOperation (.append address)
  | pop (address : Nat) : SequenceMutationOperation (.pop address)

theorem step_sequenceMutation_preserves (module : Module)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (operation : Operation) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (covered : SequenceMutationOperation operation)
    (inside : StateWithin ⟨.operation operation values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation operation values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation operation values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases covered with
  | append address =>
    rcases values with _ | ⟨value, _ | ⟨extra, rest⟩⟩
    case cons.nil =>
      exact (result_appendItem_preserves logical physical rename logicalAnchors physicalAnchors address value stack globals
        layout inside.1.1 (inside.1.2 value (by simp)) inside.2 globalsInside).protectGenerator stack inside.2
    all_goals exact (result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
      (some (.error ⟨"TypeError", []⟩)) stack globals layout inside.2 globalsInside).protectGenerator stack inside.2
  | pop address =>
    rcases values with _ | ⟨index, _ | ⟨extra, rest⟩⟩
    case nil =>
      exact (result_popItem_preserves logical physical rename logicalAnchors physicalAnchors address (.scalar (.int (-1))) stack globals
        layout inside.1.1 (by trivial) inside.2 globalsInside).protectGenerator stack inside.2
    case cons.nil =>
      exact (result_popItem_preserves logical physical rename logicalAnchors physicalAnchors address index stack globals
        layout inside.1.1 (inside.1.2 index (by simp)) inside.2 globalsInside).protectGenerator stack inside.2
    case cons.cons =>
      exact (result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (.error ⟨"TypeError", []⟩)) stack globals layout inside.2 globalsInside).protectGenerator stack inside.2

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_sequenceMutation_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (operation : Operation) (values : List Mutable.Value) (stack : List Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (covered : SequenceMutationOperation operation)
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
    (HeapCalls.Relocation.step_sequenceMutation_preserves module logical physical rename logicalAnchors physicalAnchors
      operation values stack globals layout covered ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
