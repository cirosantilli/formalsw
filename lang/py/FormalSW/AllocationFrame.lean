import lang.py.FormalSW.ConstructionFrame
import lang.py.FormalSW.BinaryHeapFrame

/-! Copies, buffer conversion and instance allocation preserve existing objects. -/
namespace FormalSW.PyAst.Heapq
open Mutable Mutable.Relocation
set_option Elab.async false

theorem preserves_allocateInstance (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (origin name : String) : Preserves invariant (Mutable.allocateInstance origin name) := by
  intro heap outcome after holds executed
  simp [Mutable.allocateInstance, Except.map] at executed
  exact executed.2 ▸ stable heap (.instance origin name []) holds

theorem preserves_allocateDataclass (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (origin name : String) (frozen : Bool) (declared : List String) (values : List Value) :
    Preserves invariant (Mutable.allocateDataclass origin name frozen declared values) := by
  intro heap outcome after holds executed
  by_cases arity : declared.length = values.length
  · simp [Mutable.allocateDataclass, arity, Except.map] at executed
    exact executed.2 ▸ stable heap (.dataInstance origin name frozen declared (declared.zip values)) holds
  · simp [Mutable.allocateDataclass, arity, Mutable.error] at executed
    exact executed.2 ▸ holds

theorem preserves_bytesElement (invariant : Heap → Prop) (value : Value) :
    Preserves invariant (Mutable.bytesElement value) := by
  unfold Mutable.bytesElement
  with_reducible repeat' first
    | exact preserves_byte invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | split

theorem preserves_bytes (invariant : Heap → Prop) (values : List Value) :
    Preserves invariant (Mutable.bytes values) := by
  unfold Mutable.bytes
  with_reducible repeat' first
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind _ _ _ (preserves_byteValues invariant _); intro bytes
    | apply Preserves.map _ _ invariant (preserves_byteValues invariant _)
    | apply Preserves.bind _ _ _ (Preserves.mapM invariant _ Mutable.bytesElement (fun value _ => preserves_bytesElement invariant value)); intro bytes
    | split

theorem preserves_bytearray (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (values : List Value) : Preserves invariant (Mutable.bytearray values) := by
  unfold Mutable.bytearray
  with_reducible repeat' first
    | exact preserves_allocateBuffer invariant stable _
    | exact Preserves.error invariant _
    | apply Preserves.bind _ _ _ (preserves_byteValues invariant _); intro bytes
    | split

theorem preserves_listConstruct (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (values : List Value) : Preserves invariant (HeapCalls.primitive (.builtin .list) values) := by
  rcases values with _ | ⟨value, _ | ⟨second, rest⟩⟩
  all_goals try cases value
  all_goals try cases rest
  all_goals simp only [HeapCalls.primitive]
  all_goals with_reducible repeat' first
    | exact preserves_allocate invariant stable _
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind _ _ _ (preserves_sequence invariant _); intro items
    | apply Preserves.bind
    | intro ignored
    | split

theorem preserves_tupleConstruct (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (values : List Value) : Preserves invariant (HeapCalls.primitive (.builtin .tuple) values) := by
  rcases values with _ | ⟨value, _ | ⟨second, rest⟩⟩
  all_goals try cases value
  all_goals try cases rest
  all_goals simp only [HeapCalls.primitive]
  all_goals with_reducible repeat' first
    | exact preserves_allocateTuple invariant stable _
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind _ _ _ (preserves_sequence invariant _); intro items
    | split

theorem preserves_reversedList (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (values : List Value) : Preserves invariant (HeapCalls.primitive .reversedList values) := by
  rcases values with _ | ⟨value, _ | ⟨second, rest⟩⟩
  all_goals try cases value
  all_goals try cases rest
  all_goals simp only [HeapCalls.primitive]
  all_goals with_reducible repeat' first
    | exact preserves_allocate invariant stable _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (preserves_sequence invariant _); intro items
    | split

theorem preserves_sorted (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (values : List Value) : Preserves invariant (HeapCalls.primitive (.builtin .sorted) values) := by
  rcases values with _ | ⟨value, _ | ⟨second, rest⟩⟩
  all_goals try cases value
  all_goals try cases rest
  all_goals simp only [HeapCalls.primitive]
  all_goals with_reducible repeat' first
    | exact preserves_allocate invariant stable _
    | exact Preserves.pure invariant _
    | exact Preserves.throw invariant _
    | exact Preserves.unsupported invariant
    | exact preserves_sequence invariant _
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind
    | intro items
    | split

theorem preserves_sortedReverse (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (values : List Value) : Preserves invariant (HeapCalls.primitive (.builtin .sortedReverse) values) := by
  rcases values with _ | ⟨value, _ | ⟨second, rest⟩⟩
  all_goals try cases value
  all_goals try cases rest
  all_goals simp only [HeapCalls.primitive]
  all_goals with_reducible repeat' first
    | exact preserves_allocate invariant stable _
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.throw invariant _
    | exact Preserves.unsupported invariant
    | exact preserves_sequence invariant _
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind _ _ _ (preserves_truth invariant _); intro reverse
    | apply Preserves.bind
    | intro items
    | split

theorem preserves_scalarResult (invariant : Heap → Prop) (result : Option (Except ExceptionObject Constant)) :
    Preserves invariant (HeapCalls.scalarResult result) := by
  cases result with
  | none => exact Preserves.unsupported invariant
  | some result =>
    cases result with
    | ok => exact Preserves.pure invariant _
    | error => exact Preserves.throw invariant _

theorem preserves_library (invariant : Heap → Prop) (module : Module) (name : String) (values : List Value) :
    Preserves invariant (HeapCalls.library module name values) := by
  unfold HeapCalls.library
  split
  · apply Preserves.bind
    · apply Preserves.mapM
      intro value _
      cases value with
      | scalar => exact Preserves.pure invariant _
      | ref => exact Preserves.error invariant "TypeError"
    · intro scalars
      exact preserves_scalarResult invariant _
  · exact Preserves.unsupported invariant

end FormalSW.PyAst.Heapq
