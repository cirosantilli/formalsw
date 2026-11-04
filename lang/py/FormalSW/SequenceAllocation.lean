import lang.py.FormalSW.MachineSequenceConstruction
import lang.py.FormalSW.ConstructionIsolation

/-! Sequence constructors preserve shallow references; tuple allocation may reuse an interned empty tuple. -/
namespace FormalSW.PyAst.Mutable.Relocation
open HeapCalls.Relocation
set_option Elab.async false

def allocateSequence (asTuple : Bool) (items : List Value) : Eval Value :=
  if asTuple then allocateTuple items else allocate items

theorem ExecutionLayout.allocateSequence {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (asTuple : Bool) (items : List Value)
    (inside : ∀ value ∈ items, value.edge.Within logical.length) (address : Nat) (after : Heap)
    (allocated : allocateSequence asTuple items logical = some (.ok (.ref address), after)) :
    ∃ other nextMap,
      allocateSequence asTuple (items.map (relocateValue rename)) physical = some (.ok (.ref (nextMap address)), other) ∧
      ExecutionLayout after other nextMap ∧ (∀ index < logical.length, nextMap index = rename index) ∧
      logical.length ≤ after.length ∧ physical.length ≤ other.length ∧ address < after.length ∧
      (∀ privateAddress object, object ≠ .tuple [] → PrivateLayout logical physical rename privateAddress object →
        PrivateLayout after other nextMap privateAddress object) := by
  cases asTuple with
  | false =>
    have equal : logical.length = address ∧ logical ++ [.list items] = after := by
      simpa [Mutable.Relocation.allocateSequence, allocate, Except.map] using allocated
    obtain ⟨left, right⟩ := equal
    subst address
    subst after
    refine ⟨physical ++ [.list (items.map (relocateValue rename))], extendMap rename logical.length physical.length,
      ?_, (layout.allocate_list items inside).2.2, extendMap_old _ _ _, by simp, by simp, by simp, ?_⟩
    · simp [Mutable.Relocation.allocateSequence, allocate, extendMap_new, Except.map]
    · intro privateAddress object _ saved
      exact (saved.allocate_list items inside).2.2
  | true =>
    obtain ⟨left, right, resultHeap, other, nextMap, leftRun, rightRun, retained, bounded, same, agree⟩ :=
      layout.allocateTuple items inside
    have equal : left = address ∧ resultHeap = after := by simpa [Mutable.Relocation.allocateSequence] using leftRun.symm.trans allocated
    obtain ⟨equalAddress, equalHeap⟩ := equal
    subst left
    subst resultHeap
    refine ⟨other, nextMap, ?_, retained, agree, allocateTuple_length logical after items (.ref address) leftRun,
      allocateTuple_length physical other _ (.ref right) rightRun, bounded, ?_⟩
    · simpa [Mutable.Relocation.allocateSequence, same] using rightRun
    · intro privateAddress object nonempty saved
      refine ⟨retained, ?_, ?_⟩
      · exact Heapq.preserves_allocateTuple (SavedCell privateAddress object) (SavedCell.allocates privateAddress object)
          (items.map (relocateValue rename)) physical (.ok (.ref right)) other saved.saved rightRun
      · exact allocateTuple_map_excludes logical physical after other rename nextMap items address right privateAddress object
          leftRun rightRun same agree saved.excludes saved.saved nonempty

end FormalSW.PyAst.Mutable.Relocation

namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation

/-- Successful collection precedes allocation. Existing tuple arguments use a stable identity step instead. -/
inductive SequenceAllocationInput (heap : Mutable.Heap) : Operation → List Value → Bool → List Value → Prop where
  | emptyList : SequenceAllocationInput heap (.builtin .list) [] false []
  | emptyTuple : SequenceAllocationInput heap (.builtin .tuple) [] true []
  | list (value : Value) (items : List Value)
      (read : positionalPool value heap = some (.ok items, heap)) :
      SequenceAllocationInput heap (.builtin .list) [value] false items
  | tuple (value : Value) (items : List Value)
      (read : positionalPool value heap = some (.ok items, heap))
      (notTuple : ∀ address contents, value = .ref address → heap[address]? ≠ some (.tuple contents)) :
      SequenceAllocationInput heap (.builtin .tuple) [value] true items
  | reverse (value : Value) (items : List Value)
      (read : Mutable.sequence value heap = some (.ok items, heap)) :
      SequenceAllocationInput heap .reversedList [value] false items.reverse

theorem SequenceAllocationInput.within {heap : Mutable.Heap} {operation : Operation} {values items : List Value} {asTuple : Bool}
    (input : SequenceAllocationInput heap operation values asTuple items) (closed : Closed heap)
    (inside : ∀ value ∈ values, value.edge.Within heap.length) : ∀ value ∈ items, value.edge.Within heap.length := by
  cases input with
  | emptyList | emptyTuple => simp
  | list value items read | tuple value items read =>
    exact sequence_items_within heap heap closed value items (positionalPool_sequence heap value items read)
  | reverse value items read =>
    intro item member
    exact sequence_items_within heap heap closed value items read item (List.mem_reverse.mp member)

theorem SequenceAllocationInput.relocates {logical physical : Mutable.Heap} {rename : Nat → Nat}
    {operation : Operation} {values items : List Value} {asTuple : Bool}
    (input : SequenceAllocationInput logical operation values asTuple items) (layout : ExecutionLayout logical physical rename)
    (inside : ∀ value ∈ values, value.edge.Within logical.length) :
    SequenceAllocationInput physical operation (values.map (relocateValue rename)) asTuple (items.map (relocateValue rename)) := by
  cases input with
  | emptyList => exact .emptyList
  | emptyTuple => exact .emptyTuple
  | list value items read =>
    apply SequenceAllocationInput.list
    simpa only [read, Option.map, Except.map] using positionalPool_relocates layout.runtime value (inside value (by simp))
  | tuple value items read notTuple =>
    apply SequenceAllocationInput.tuple
    · simpa only [read, Option.map, Except.map] using positionalPool_relocates layout.runtime value (inside value (by simp))
    · intro address contents equal
      cases value with
      | scalar => cases equal
      | ref source =>
        have bound := inside (.ref source) (by simp)
        have found : logical[source]? = some logical[source] := List.getElem?_eq_getElem bound
        have moved := layout.runtime.lookup source _ found
        cases equal
        cases object : logical[source] <;> simp only [object, relocateObject] at moved
        all_goals first
          | exact False.elim (notTuple source _ rfl (found.trans (congrArg some object)))
          | simp [moved]
  | reverse value items read =>
    rw [List.map_reverse]
    apply SequenceAllocationInput.reverse
    simpa only [read, Option.map, Except.map] using layout.runtime.sequence value (inside value (by simp))

theorem SequenceAllocationInput.operation_relocates {heap : Mutable.Heap} {operation : Operation}
    {values items : List Value} {asTuple : Bool} (input : SequenceAllocationInput heap operation values asTuple items)
    (rename : Nat → Nat) : relocateRuntimeOperation rename operation = operation := by
  cases input <;> rfl

theorem SequenceAllocationInput.primitive {heap : Mutable.Heap} {operation : Operation}
    {values items : List Value} {asTuple : Bool} (input : SequenceAllocationInput heap operation values asTuple items) :
    HeapCalls.primitive operation values heap = allocateSequence asTuple items heap := by
  cases input with
  | emptyList | emptyTuple => rfl
  | list value items read => simp [primitive_list_copy, sequenceCopy, read, Mutable.eval_bind, allocateSequence]
  | tuple value items read notTuple =>
    rw [primitive_tuple_copy]
    cases value with
    | scalar => simp [sequenceCopy, read, Mutable.eval_bind, allocateSequence]
    | ref address =>
      cases found : heap[address]? with
      | none => simp [found, sequenceCopy, read, Mutable.eval_bind, allocateSequence]
      | some object =>
        cases object <;> first
          | exact False.elim (notTuple address _ rfl found)
          | simp [found, sequenceCopy, read, Mutable.eval_bind, allocateSequence]
  | reverse value items read =>
    change (do let items ← Mutable.sequence value; Mutable.allocate items.reverse) heap = _
    simp [read, Mutable.eval_bind, allocateSequence]

end FormalSW.PyAst.HeapCalls.Relocation
