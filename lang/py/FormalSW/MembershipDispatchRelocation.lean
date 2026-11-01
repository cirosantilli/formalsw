import lang.py.FormalSW.SequenceMembershipRelocation

/-! All modeled membership branches preserve completed outcomes and caller memory. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

theorem RuntimeLayout.bytesContains {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (needle : Value) (bytes : List UInt8)
    (inside : needle.edge.Within logical.length) :
    HeapCalls.bytesContains (relocateValue rename needle) bytes physical =
      (HeapCalls.bytesContains needle bytes logical).map (fun pair => (pair.1, physical)) := by
  cases needle with
  | scalar scalar =>
    cases scalar <;> simp [HeapCalls.bytesContains, relocateValue, HeapCalls.bytesContainsInteger, error]
    all_goals split <;> rfl
  | ref address =>
    have found := List.getElem?_eq_getElem inside
    generalize objectValue : logical[address] = object at found
    have moved := layout.lookup address object found
    cases object <;> simp [HeapCalls.bytesContains, relocateValue, found, moved, relocateObject, error, unsupported]

theorem bytesContains_keeps_heap (heap after : Heap) (needle : Value) (bytes : List UInt8)
    (inside : needle.edge.Within heap.length) (outcome : Except ExceptionObject Bool)
    (executed : HeapCalls.bytesContains needle bytes heap = some (outcome, after)) : after = heap := by
  have same := (RuntimeLayout.refl heap).bytesContains needle bytes inside
  simp only [relocateValue_id, executed, Option.map_some] at same
  exact congrArg Prod.snd (Option.some.inj same)

theorem RuntimeLayout.membership_bytes {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (needle : Value) (bytes : List UInt8) (negated : Bool)
    (inside : needle.edge.Within logical.length) :
    HeapCalls.membership (relocateValue rename needle) (.scalar (.bytes bytes)) negated physical =
      (HeapCalls.membership needle (.scalar (.bytes bytes)) negated logical).map
        (fun pair => (pair.1.map (relocateValue rename), physical)) := by
  have query := layout.bytesContains needle bytes inside
  cases searched : HeapCalls.bytesContains needle bytes logical with
  | none => simp [HeapCalls.membership, query, searched]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have unchanged := bytesContains_keeps_heap logical after needle bytes inside outcome searched
    subst after
    cases outcome <;> simp [HeapCalls.membership, query, searched, Except.map]
    rfl

theorem membership_bytearray_eq (heap : Heap) (needle : Value) (address : Nat) (bytes : List UInt8)
    (negated : Bool) (found : heap[address]? = some (.bytearray bytes)) :
    HeapCalls.membership needle (.ref address) negated heap =
      HeapCalls.membership needle (.scalar (.bytes bytes)) negated heap := by
  simp [HeapCalls.membership, found]

theorem RuntimeLayout.membership_bytearray {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (needle : Value) (address : Nat) (bytes : List UInt8)
    (negated : Bool) (found : logical[address]? = some (.bytearray bytes))
    (inside : needle.edge.Within logical.length) :
    HeapCalls.membership (relocateValue rename needle) (.ref (rename address)) negated physical =
      (HeapCalls.membership needle (.ref address) negated logical).map
        (fun pair => (pair.1.map (relocateValue rename), physical)) := by
  rw [membership_bytearray_eq logical needle address bytes negated found,
    membership_bytearray_eq physical (relocateValue rename needle) (rename address) bytes negated (layout.lookup address _ found)]
  exact layout.membership_bytes needle bytes negated inside

theorem RuntimeLayout.membership_scalar {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (needle : Value) (container : Constant) (negated : Bool)
    (inside : needle.edge.Within logical.length) :
    HeapCalls.membership (relocateValue rename needle) (.scalar container) negated physical =
      (HeapCalls.membership needle (.scalar container) negated logical).map
        (fun pair => (pair.1.map (relocateValue rename), physical)) := by
  cases container with
  | bytes bytes => exact layout.membership_bytes needle bytes negated inside
  | bool value | int value | none => simp [HeapCalls.membership, error, Except.map]
  | string text =>
    cases needle with
    | ref address => simp [HeapCalls.membership, relocateValue, error, Except.map]
    | scalar scalar => cases scalar <;> simp [HeapCalls.membership, relocateValue, error, Except.map]

/-- Completed `in` and `not in` use the same rule for every modeled operand kind. -/
theorem RuntimeLayout.membership {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (needle container : Value) (negated : Bool)
    (needleInside : needle.edge.Within logical.length) (containerInside : container.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : HeapCalls.membership needle container negated logical = some (outcome, after)) :
    HeapCalls.membership (relocateValue rename needle) (relocateValue rename container) negated physical =
      some (outcome.map (relocateValue rename), physical) := by
  have transport (same : HeapCalls.membership (relocateValue rename needle) (relocateValue rename container) negated physical =
      (HeapCalls.membership needle container negated logical).map
        (fun pair => (pair.1.map (relocateValue rename), physical))) :
      HeapCalls.membership (relocateValue rename needle) (relocateValue rename container) negated physical =
        some (outcome.map (relocateValue rename), physical) := by rw [same, executed]; rfl
  cases container with
  | scalar scalar => exact transport (layout.membership_scalar needle scalar negated needleInside)
  | ref address =>
    have found := List.getElem?_eq_getElem containerInside
    generalize objectValue : logical[address] = object at found
    cases object with
    | list items => exact (layout.membership_sequences closed false needle address items negated found needleInside _ _ executed).2
    | tuple items => exact (layout.membership_sequences closed true needle address items negated found needleInside _ _ executed).2
    | bytearray bytes => exact transport (layout.membership_bytearray needle address bytes negated found needleInside)
    | set items => exact transport (layout.membership_set closed address items needle negated found needleInside)
    | keySet items => exact transport (layout.membership_keySet closed address items needle negated found needleInside)
    | dict entries => exact transport (layout.membership_dict closed address entries needle negated found needleInside)
    | keyDict entries => exact transport (layout.membership_keyDict closed address entries needle negated found needleInside)
    | «instance» origin name fields | dataInstance origin name frozen declared fields =>
      simp [HeapCalls.membership, found, unsupported] at executed

theorem membership_keeps_heap (heap after : Heap) (closed : Closed heap) (needle container : Value) (negated : Bool)
    (needleInside : needle.edge.Within heap.length) (containerInside : container.edge.Within heap.length)
    (outcome : Except ExceptionObject Value)
    (executed : HeapCalls.membership needle container negated heap = some (outcome, after)) : after = heap := by
  have same := (RuntimeLayout.refl heap).membership closed needle container negated needleInside containerInside _ _ executed
  simp only [relocateValue_id, executed] at same
  exact congrArg Prod.snd (Option.some.inj same)

/-- The final membership continuation produces a Boolean, independently of how the search ran. -/
theorem boolean_bind_value {α : Type} (action : Eval α) (answer : α → Bool) (heap after : Heap) (value : Value)
    (executed : (do
      let found ← action
      pure (Value.scalar (.bool (answer found)))) heap = some (.ok value, after)) :
    ∃ answer, value = .scalar (.bool answer) := by
  rw [eval_bind] at executed
  cases queried : action heap with
  | none => simp [queried] at executed
  | some pair =>
    rcases pair with ⟨outcome, middle⟩
    cases outcome with
    | error exception => simp [queried] at executed
    | ok found =>
      have same : Value.scalar (.bool (answer found)) = value ∧ middle = after := by
        simpa [queried] using executed
      exact ⟨_, same.1.symm⟩

theorem membership_value (heap after : Heap) (needle container : Value) (negated : Bool) (value : Value)
    (executed : HeapCalls.membership needle container negated heap = some (.ok value, after)) :
    ∃ answer, value = .scalar (.bool answer) := by
  unfold HeapCalls.membership at executed
  cases container with
  | scalar scalar =>
    cases scalar <;> cases needle
    all_goals first
      | exact boolean_bind_value _ _ heap after value executed
      | rename_i scalar
        cases scalar <;> exact boolean_bind_value _ _ heap after value executed
  | ref address =>
    simp only [eval_bind, eval_get] at executed
    dsimp only [bind, Option.bind] at executed
    cases found : heap[address]? with
    | none =>
      rw [found] at executed
      exact boolean_bind_value _ _ heap after value executed
    | some object =>
      rw [found] at executed
      cases object <;> cases needle <;> exact boolean_bind_value _ _ heap after value executed

theorem ExecutionLayout.membership {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (needle container : Value) (negated : Bool)
    (needleInside : needle.edge.Within logical.length) (containerInside : container.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : HeapCalls.membership needle container negated logical = some (outcome, after)) :
    HeapCalls.membership (relocateValue rename needle) (relocateValue rename container) negated physical =
        some (outcome.map (relocateValue rename), physical) ∧ ExecutionLayout after physical rename ∧
      (∀ value, outcome = .ok value → value.edge.Within after.length) := by
  have unchanged := membership_keeps_heap logical after layout.closed needle container negated needleInside containerInside _ executed
  refine ⟨layout.runtime.membership layout.closed needle container negated needleInside containerInside _ _ executed,
    unchanged ▸ layout, ?_⟩
  intro value success
  rw [success] at executed
  obtain ⟨answer, rfl⟩ := membership_value logical after needle container negated value executed
  trivial

end FormalSW.PyAst.Mutable.Relocation
