import lang.py.FormalSW.MachineDictionaryMethods
import lang.py.FormalSW.MachineConstructionInvariant
import lang.py.FormalSW.PositionalRelocation

/-! Sequence conversion retains shallow aliases, tuple identity and allocation order. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

theorem result_allocateList_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (items : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (itemsInside : ∀ value ∈ items, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (Mutable.allocate items) stack globals)
      (result physicalAnchors physical (Mutable.allocate (items.map (relocateValue rename)))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  obtain ⟨left, right, retained⟩ := layout.allocate_list items itemsInside
  apply result_preserves logical physical _ _ rename (extendMap rename logical.length physical.length)
    logicalAnchors physicalAnchors _ _ stack globals (.ok (.ref logical.length))
    (extendMap_old _ _ _) (by simp) (by simp) retained stackInside globalsInside
  · intro value same; cases same; simp [Mutable.Value.edge, Graph.Edge.Within]
  · exact left
  · simpa only [Except.map, relocateValue, extendMap_new] using right

theorem result_allocateTuple_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (items : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (itemsInside : ∀ value ∈ items, value.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (Mutable.allocateTuple items) stack globals)
      (result physicalAnchors physical (Mutable.allocateTuple (items.map (relocateValue rename)))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  obtain ⟨address, otherAddress, after, other, nextMap, left, right, retained, bounded, same, agree⟩ :=
    layout.allocateTuple items itemsInside
  apply result_preserves logical physical after other rename nextMap logicalAnchors physicalAnchors _ _ stack globals
    (.ok (.ref address)) agree (allocateTuple_length logical after items (.ref address) left)
    (allocateTuple_length physical other _ (.ref otherAddress) right) retained stackInside globalsInside
  · intro value equal; cases equal; exact bounded
  · exact left
  · simpa only [Except.map, relocateValue, same] using right

def sequenceCopy (asTuple : Bool) (source : Value) : Mutable.Eval Value := do
  let items ← positionalPool source
  if asTuple then Mutable.allocateTuple items else Mutable.allocate items

theorem result_sequenceCopy_preserves (asTuple : Bool) (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (source : Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (sourceInside : source.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (sequenceCopy asTuple source) stack globals)
      (result physicalAnchors physical (sequenceCopy asTuple (relocateValue rename source))
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  simp only [sequenceCopy, result_bind]
  apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _ (List.map (relocateValue rename))
    _ _ globals layout globalsInside
    (fun outcome after executed => positionalPool_keeps_heap logical source outcome after executed)
    (positionalPool_relocates layout.runtime source sourceInside)
  intro items read
  have bounded := sequence_items_within logical logical layout.closed source items (positionalPool_sequence logical source items read)
  cases asTuple with
  | false => exact result_allocateList_preserves logical physical rename logicalAnchors physicalAnchors items stack globals layout bounded stackInside globalsInside
  | true => exact result_allocateTuple_preserves logical physical rename logicalAnchors physicalAnchors items stack globals layout bounded stackInside globalsInside

theorem primitive_list_copy (heap : Mutable.Heap) (source : Value) :
    primitive (.builtin .list) [source] heap = sequenceCopy false source heap := by
  cases source with
  | scalar scalar => rfl
  | ref address =>
    cases found : heap[address]? with
    | none => simp [primitive, sequenceCopy, positionalPool, found, Mutable.eval_bind]
    | some object => cases object <;> simp [primitive, sequenceCopy, positionalPool, found, Mutable.eval_bind, Mutable.unsupported]

theorem primitive_tuple_copy (heap : Mutable.Heap) (source : Value) :
    primitive (.builtin .tuple) [source] heap = match source with
      | .ref address => match heap[address]? with
          | some (.tuple _) => some (.ok source, heap)
          | _ => sequenceCopy true source heap
      | _ => sequenceCopy true source heap := by
  cases source with
  | scalar scalar => rfl
  | ref address =>
    cases found : heap[address]? with
    | none => simp [primitive, sequenceCopy, positionalPool, found, Mutable.eval_bind]
    | some object => cases object <;> simp [primitive, sequenceCopy, positionalPool, found, Mutable.eval_bind, Mutable.unsupported]

theorem result_listCopy_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (source : Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (sourceInside : source.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (primitive (.builtin .list) [source]) stack globals)
      (result physicalAnchors physical (primitive (.builtin .list) [relocateValue rename source])
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  simpa only [result, run, primitive_list_copy] using
    result_sequenceCopy_preserves false logical physical rename logicalAnchors physicalAnchors source stack globals layout sourceInside stackInside globalsInside

theorem result_tupleCopy_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (source : Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (sourceInside : source.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (primitive (.builtin .tuple) [source]) stack globals)
      (result physicalAnchors physical (primitive (.builtin .tuple) [relocateValue rename source])
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  have copied := result_sequenceCopy_preserves true logical physical rename logicalAnchors physicalAnchors source stack globals layout sourceInside stackInside globalsInside
  cases source with
  | scalar scalar => simpa only [result, run, primitive_tuple_copy, relocateValue] using copied
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem sourceInside
    have moved := layout.runtime.lookup address _ found
    cases object : logical[address] <;> simp only [object, relocateObject] at moved
    case tuple items =>
      simpa only [result, run, primitive_tuple_copy, relocateValue, found, object, moved, Mutable.eval_pure] using
        result_pure_preserves logical physical rename logicalAnchors physicalAnchors (.ref address) stack globals layout sourceInside stackInside
    all_goals simpa only [result, run, primitive_tuple_copy, relocateValue, found, object, moved] using copied

theorem result_reversedList_preserves (logical physical : Mutable.Heap) (rename : Nat → Nat)
    (logicalAnchors physicalAnchors : Nat) (source : Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (sourceInside : source.edge.Within logical.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin logical.length frame) (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (result logicalAnchors logical (primitive .reversedList [source]) stack globals)
      (result physicalAnchors physical (primitive .reversedList [relocateValue rename source])
        (stack.map (relocateFrame rename)) (relocateGlobals rename globals)) := by
  change Preserves logical physical rename physicalAnchors
    (result logicalAnchors logical (do let items ← Mutable.sequence source; Mutable.allocate items.reverse) stack globals)
    (result physicalAnchors physical (do let items ← Mutable.sequence (relocateValue rename source); Mutable.allocate items.reverse)
      (stack.map (relocateFrame rename)) (relocateGlobals rename globals))
  rw [result_bind, result_bind]
  apply run_readonly_preserves logical physical rename logicalAnchors physicalAnchors _ _ (List.map (relocateValue rename))
    _ _ globals layout globalsInside
    (fun outcome after executed => sequence_keeps_heap logical after source outcome executed)
    (layout.runtime.sequence source sourceInside)
  intro items read
  have bounded : ∀ value ∈ items.reverse, value.edge.Within logical.length := by
    intro value member
    exact sequence_items_within logical logical layout.closed source items read value (List.mem_reverse.mp member)
  simpa only [List.map_reverse] using
    result_allocateList_preserves logical physical rename logicalAnchors physicalAnchors items.reverse stack globals layout bounded stackInside globalsInside

inductive SequenceConstructionOperation : Operation → Prop
  | listDisplay : SequenceConstructionOperation .list
  | tupleDisplay : SequenceConstructionOperation .tuple
  | list : SequenceConstructionOperation (.builtin .list)
  | tuple : SequenceConstructionOperation (.builtin .tuple)
  | reverse : SequenceConstructionOperation .reversedList

theorem step_sequenceConstruction_preserves (module : Module)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors : Nat)
    (operation : Operation) (values : List Value) (stack : List Frame) (globals : Mutable.Globals)
    (layout : ExecutionLayout logical physical rename) (covered : SequenceConstructionOperation operation)
    (inside : StateWithin ⟨.operation operation values, stack, logical⟩)
    (globalsInside : GlobalsWithin logical.length globals) :
    Preserves logical physical rename physicalAnchors
      (step module logicalAnchors ⟨.operation operation values, stack, logical⟩ globals)
      (step module physicalAnchors (relocateState rename physical ⟨.operation operation values, stack, logical⟩)
        (relocateGlobals rename globals)) := by
  cases covered with
  | listDisplay =>
    exact (result_allocateList_preserves logical physical rename logicalAnchors physicalAnchors values stack globals
      layout inside.1.2 inside.2 globalsInside).protectGenerator stack inside.2
  | list =>
    rcases values with _ | ⟨source, _ | ⟨extra, rest⟩⟩
    case nil =>
      exact (result_allocateList_preserves logical physical rename logicalAnchors physicalAnchors [] stack globals
        layout (by simp) inside.2 globalsInside).protectGenerator stack inside.2
    case cons.nil =>
      exact (result_listCopy_preserves logical physical rename logicalAnchors physicalAnchors source stack globals
        layout (inside.1.2 source (by simp)) inside.2 globalsInside).protectGenerator stack inside.2
    case cons.cons =>
      exact (result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (.error ⟨"TypeError", []⟩)) stack globals layout inside.2 globalsInside).protectGenerator stack inside.2
  | tupleDisplay =>
    exact (result_allocateTuple_preserves logical physical rename logicalAnchors physicalAnchors values stack globals
      layout inside.1.2 inside.2 globalsInside).protectGenerator stack inside.2
  | tuple =>
    rcases values with _ | ⟨source, _ | ⟨extra, rest⟩⟩
    case nil =>
      exact (result_allocateTuple_preserves logical physical rename logicalAnchors physicalAnchors [] stack globals
        layout (by simp) inside.2 globalsInside).protectGenerator stack inside.2
    case cons.nil =>
      exact (result_tupleCopy_preserves logical physical rename logicalAnchors physicalAnchors source stack globals
        layout (inside.1.2 source (by simp)) inside.2 globalsInside).protectGenerator stack inside.2
    case cons.cons =>
      exact (result_scalar_preserves logical physical rename logicalAnchors physicalAnchors
        (some (.error ⟨"TypeError", []⟩)) stack globals layout inside.2 globalsInside).protectGenerator stack inside.2
  | reverse =>
    rcases values with _ | ⟨source, _ | ⟨extra, rest⟩⟩
    case cons.nil =>
      exact (result_reversedList_preserves logical physical rename logicalAnchors physicalAnchors source stack globals
        layout (inside.1.2 source (by simp)) inside.2 globalsInside).protectGenerator stack inside.2
    all_goals exact Preserves.unchanged layout (by trivial) (by trivial) rfl

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.IteratorCalls.Relocation
open HeapCalls HeapCalls.Relocation Mutable.Relocation

theorem step_sequenceConstruction_preserves (module : Module) (choices : ChoiceSchedule)
    (logical physical : Mutable.Heap) (rename : Nat → Nat) (logicalAnchors physicalAnchors used : Nat)
    (operation : Operation) (values : List Mutable.Value) (stack : List Frame) (resumes : List Resume)
    (globals : Mutable.Globals) (source : ModuleSource module) (layout : ExecutionLayout logical physical rename)
    (covered : SequenceConstructionOperation operation)
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
    (HeapCalls.Relocation.step_sequenceConstruction_preserves module logical physical rename logicalAnchors physicalAnchors
      operation values stack globals layout covered ⟨inside.1, inside.2.1⟩ globalsInside)

end FormalSW.PyAst.IteratorCalls.Relocation
