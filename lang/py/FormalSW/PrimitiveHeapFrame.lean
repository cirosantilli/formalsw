import lang.py.FormalSW.ReadHeapFrame

/-! Primitive effects retain predicates stable under allocation and their designated receiver writes. -/
namespace FormalSW.PyAst.Heapq
open Mutable Mutable.Relocation HeapCalls
set_option Elab.async false

/-- Only the first argument can be the receiver of an argument-based mutation. -/
def receiverTargets : List Value → List Nat
  | .ref address :: _ => [address]
  | _ => []

def builtinTargets (builtin : Builtin) (values : List Value) : List Nat :=
  match builtin with
  | .heapqHeapify | .heapqPush | .heapqPop => receiverTargets values
  | _ => []

/-- An overapproximation includes the receiver even when argument validation prevents the write. -/
def primitiveTargets (operation : Operation) (values : List Value) : List Nat :=
  match operation with
  | .append address | .pop address | .sort address | .sortReverse address | .add address
    | .dictionarySetDefault address | .dictionaryClear address => [address]
  | .setField _ _ | .setItem _ | .setSlice _ => receiverTargets values
  | .builtin builtin => builtinTargets builtin values
  | _ => []

theorem preserves_heapify_values (invariant : Heap → Prop) (values : List Value)
    (updates : ∀ address ∈ receiverTargets values, UpdateInvariant address invariant) :
    Preserves invariant (heapify values) := by
  rcases values with _ | ⟨first, _ | ⟨second, rest⟩⟩
  · exact Preserves.error invariant "TypeError"
  · cases first with
    | scalar scalar =>
      intro heap outcome after holds executed
      simp [heapify, receiver, Mutable.error, Mutable.eval_bind] at executed
      exact executed.2 ▸ holds
    | ref address => exact preserves_heapify address invariant ((updates address (by simp [receiverTargets])).swaps address invariant)
  · exact Preserves.error invariant "TypeError"

theorem preserves_heappush_values (invariant : Heap → Prop) (values : List Value)
    (updates : ∀ address ∈ receiverTargets values, UpdateInvariant address invariant) :
    Preserves invariant (heappush values) := by
  rcases values with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
  · exact Preserves.error invariant "TypeError"
  · exact Preserves.error invariant "TypeError"
  · cases first with
    | scalar scalar =>
      intro heap outcome after holds executed
      simp [heappush, receiver, Mutable.error, Mutable.eval_bind] at executed
      exact executed.2 ▸ holds
    | ref address => exact preserves_heappush address invariant (updates address (by simp [receiverTargets])) second
  · exact Preserves.error invariant "TypeError"

theorem preserves_heappop_values (invariant : Heap → Prop) (values : List Value)
    (updates : ∀ address ∈ receiverTargets values, UpdateInvariant address invariant) :
    Preserves invariant (heappop values) := by
  rcases values with _ | ⟨first, _ | ⟨second, rest⟩⟩
  · exact Preserves.error invariant "TypeError"
  · cases first with
    | scalar scalar =>
      intro heap outcome after holds executed
      simp [heappop, receiver, Mutable.error, Mutable.eval_bind] at executed
      exact executed.2 ▸ holds
    | ref address => exact preserves_heappop address invariant (updates address (by simp [receiverTargets]))
  · exact Preserves.error invariant "TypeError"

theorem preserves_scalarRepresentation (invariant : Heap → Prop) (values : List Value) :
    Preserves invariant (scalarRepresentation values) := by
  unfold scalarRepresentation
  with_reducible repeat' first
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | split

theorem preserves_builtin (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (builtin : Builtin) (values : List Value)
    (updates : ∀ address ∈ builtinTargets builtin values, UpdateInvariant address invariant) :
    Preserves invariant (primitive (.builtin builtin) values) := by
  cases builtin
  all_goals first
    | exact preserves_listConstruct invariant stable values
    | exact preserves_tupleConstruct invariant stable values
    | exact preserves_setConstruct invariant stable values
    | exact preserves_allocateSetValues invariant stable values
    | exact preserves_dictionaryConstruct invariant stable values
    | exact preserves_bytearray invariant stable values
    | exact preserves_bytes invariant values
    | exact preserves_sorted invariant stable values
    | exact preserves_sortedReverse invariant stable values
    | exact preserves_scalarRepresentation invariant values
    | exact preserves_divmod invariant stable values
    | exact preserves_heapify_values invariant values updates
    | exact preserves_heappush_values invariant values updates
    | exact preserves_heappop_values invariant values updates
    | skip
  all_goals rcases values with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
  all_goals try cases first
  all_goals try cases second
  all_goals try cases third
  all_goals try cases rest
  all_goals simp only [primitive]
  all_goals with_reducible repeat' first
    | exact preserves_identity invariant _ _
    | exact preserves_length invariant _
    | exact preserves_scalarResult invariant _
    | exact preserves_sequence invariant _
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind
    | apply Preserves.mapM
    | intro item
    | split

theorem preserves_writeField_scalar (invariant : Heap → Prop) (scalar : Constant) (name : String) (value : Value) :
    Preserves invariant (Mutable.writeField (.scalar scalar) name value) := by
  unfold Mutable.writeField
  split
  · exact Preserves.unsupported invariant
  · apply Preserves.bind _ _ _ (preserves_instanceData invariant (.scalar scalar))
    rintro ⟨origin, className, fields⟩
    exact Preserves.error invariant "AttributeError"

theorem preserves_isDigit (invariant : Heap → Prop) (receiver : Value) (values : List Value) :
    Preserves invariant (primitive (.isDigit receiver) values) := by
  cases receiver with
  | scalar scalar =>
    cases scalar <;> cases values <;> first
      | exact Preserves.pure invariant _
      | exact Preserves.error invariant "TypeError"
  | ref address =>
    cases values with
    | cons => exact Preserves.error invariant "TypeError"
    | nil =>
      apply Preserves.bind _ _ _ (Preserves.get invariant)
      intro heap
      cases heap[address]? with
      | none => exact Preserves.unsupported invariant
      | some object => cases object <;> first
          | exact Preserves.pure invariant _
          | exact Preserves.unsupported invariant

theorem preserves_replace (invariant : Heap → Prop) (text : String) (values : List Value) :
    Preserves invariant (primitive (.replace text) values) := by
  rcases values with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
  all_goals try cases first
  all_goals try cases second
  all_goals try cases third
  all_goals try cases rest
  all_goals first
    | exact preserves_scalarResult invariant _
    | exact Preserves.error invariant "TypeError"
    | skip
  all_goals cases ‹Constant› <;> cases ‹Constant›
  all_goals simp only [primitive]
  all_goals with_reducible repeat' first
    | exact Preserves.error invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | split

theorem preserves_dictionarySingleton (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (key value : Value) : Preserves invariant (DictionaryDisplay.singleton key value) := by
  unfold DictionaryDisplay.singleton
  apply Preserves.bind _ _ _ (preserves_hashKey invariant key)
  intro hashed
  apply Preserves.bind _ _ _ (Preserves.get invariant)
  intro heap
  apply Preserves.bind _ _ _ (Preserves.modify invariant _ (fun before held => stable before _ held))
  intro _
  exact Preserves.pure invariant _

set_option maxHeartbeats 1200000 in
/-- The actual primitive may allocate, read any object, and update only its listed receivers. -/
theorem preserves_primitive (invariant : Heap → Prop) (stable : AppendInvariant invariant)
    (operation : Operation) (values : List Value)
    (updates : ∀ address ∈ primitiveTargets operation values, UpdateInvariant address invariant) :
    Preserves invariant (primitive operation values) := by
  cases operation
  all_goals first
    | exact preserves_builtin invariant stable _ values updates
    | exact preserves_isDigit invariant _ values
    | exact preserves_replace invariant _ values
    | exact preserves_allocate invariant stable values
    | exact preserves_allocateTuple invariant stable values
    | exact preserves_reversedList invariant stable values
    | exact Preserves.unsupported invariant
    | skip
  all_goals rcases values with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
  all_goals try cases first
  all_goals try cases rest
  all_goals simp [primitiveTargets, receiverTargets] at updates
  all_goals first
    | exact preserves_sort _ invariant updates
    | exact preserves_sortReverse _ invariant updates _
    | skip
  all_goals simp only [primitive]
  all_goals with_reducible repeat' first
    | exact preserves_writeField_scalar invariant _ _ _
    | exact preserves_membership invariant _ _ _
    | exact preserves_getItem invariant _ _
    | exact preserves_getSlice invariant stable _ _ _ _
    | exact preserves_setItem _ invariant updates _ _
    | exact preserves_setSlice _ invariant updates _ _ _ _
    | exact preserves_writeField _ invariant updates _ _
    | exact preserves_dictionaryGet invariant _ _ _
    | exact preserves_dictionarySingleton invariant stable _ _
    | exact preserves_dictionarySetDefault _ invariant updates _ _
    | exact preserves_clearDictionary _ invariant updates
    | exact preserves_appendItem _ invariant updates _
    | exact preserves_popItem _ invariant updates _
    | exact preserves_addItem _ invariant updates _
    | exact preserves_allocate invariant stable _
    | exact preserves_scalarResult invariant _
    | exact preserves_sequence invariant _
    | exact Preserves.pure invariant _
    | exact Preserves.error invariant _
    | exact Preserves.throw invariant _
    | exact Preserves.unsupported invariant
    | apply Preserves.bind _ _ _ (Preserves.get invariant); intro heap
    | apply Preserves.bind
    | apply Preserves.mapM
    | intro item
    | split

  all_goals exact Preserves.error invariant "TypeError"

end FormalSW.PyAst.Heapq
