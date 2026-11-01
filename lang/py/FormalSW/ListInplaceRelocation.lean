import lang.py.FormalSW.MachineBinary

/-! Augmented list operations mutate the original object while retaining shared elements. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

/-- Builtin extension consumes its sequence before replacing the destination contents. -/
theorem inplace_add_list_eval (heap : Mutable.Heap) (address : Nat) (items : List Value) (right : Value)
    (found : heap[address]? = some (.list items)) :
    inplace .add (.ref address) right heap =
      (do
        let more ← Mutable.sequence right
        modify fun heap => heap.set address (.list (items ++ more))
        pure (.ref address) : Mutable.Eval Value) heap := by
  cases right with
  | ref other =>
    simp [inplace, found]
    change (do
      let old ← Mutable.array (.ref address)
      let more ← Mutable.sequence (.ref other)
      modify fun heap => heap.set address (.list (old.2 ++ more))
      pure (.ref address) : Mutable.Eval Value) heap = _
    simp [Mutable.array, found, Mutable.eval_bind]
  | scalar scalar =>
    cases scalar with
    | int | bool | none => simp [inplace, found]; rfl
    | string text =>
      simp [inplace, found]
      change (do
        let old ← Mutable.array (.ref address)
        modify fun heap => heap.set address (.list (old.2 ++ text.toList.map
          (fun c => .scalar (.string (String.singleton c)))))
        pure (.ref address) : Mutable.Eval Value) heap = _
      simp [Mutable.array, Mutable.sequence, found, Except.map]
    | bytes bytes =>
      simp [inplace, found]
      change (do
        let old ← Mutable.array (.ref address)
        modify fun heap => heap.set address (.list (old.2 ++ bytes.map (fun byte => .scalar (.int byte.toNat))))
        pure (.ref address) : Mutable.Eval Value) heap = _
      simp [Mutable.array, Mutable.sequence, found, Except.map]

theorem inplace_mult_list_eval (heap : Mutable.Heap) (address : Nat) (items : List Value) (count : Int)
    (found : heap[address]? = some (.list items)) :
    inplace .mult (.ref address) (.scalar (.int count)) heap =
      some (.ok (.ref address), heap.set address (.list (List.replicate count.toNat items).flatten)) := by
  simp [inplace, found]
  change (do
    let old ← Mutable.array (.ref address)
    modify fun heap => heap.set address (.list (List.replicate count.toNat old.2).flatten)
    pure (.ref address) : Mutable.Eval Value) heap = _
  simp [Mutable.array, found, Except.map]

theorem inplace_mult_list_bool_eval (heap : Mutable.Heap) (address : Nat) (items : List Value) (keep : Bool)
    (found : heap[address]? = some (.list items)) :
    inplace .mult (.ref address) (.scalar (.bool keep)) heap =
      some (.ok (.ref address), heap.set address (.list (if keep then items else []))) := by
  simp [inplace, found]
  change (do
    let old ← Mutable.array (.ref address)
    modify fun heap => heap.set address (.list (if keep then old.2 else []))
    pure (.ref address) : Mutable.Eval Value) heap = _
  simp [Mutable.array, found, Except.map]

/-- Invalid builtin counts fail before mutation; integers and Booleans share the integer model. -/
theorem inplace_mult_list_value_eval (heap : Mutable.Heap) (address : Nat) (items : List Value) (right : Value)
    (found : heap[address]? = some (.list items)) :
    inplace .mult (.ref address) right heap =
      (do
        let count ← Mutable.integer right
        modify fun heap => heap.set address (.list (List.replicate count.toNat items).flatten)
        pure (.ref address) : Mutable.Eval Value) heap := by
  cases right with
  | ref other => simp [inplace, found]; rfl
  | scalar scalar =>
    cases scalar with
    | int count =>
      rw [inplace_mult_list_eval heap address items count found]
      simp [Mutable.integer, Except.map]
    | bool keep =>
      rw [inplace_mult_list_bool_eval heap address items keep found]
      cases keep <;> simp [Mutable.integer, Except.map]
    | string | bytes | none => simp [inplace, found]; rfl

end FormalSW.PyAst.HeapCalls.Relocation

namespace FormalSW.PyAst.Mutable.Relocation
open HeapCalls.Relocation
set_option Elab.async false

theorem sequence_keeps_heap (heap after : Heap) (value : Value) (outcome : Except ExceptionObject (List Value))
    (executed : Mutable.sequence value heap = some (outcome, after)) : after = heap := by
  cases value with
  | scalar scalar =>
    cases scalar <;> simp [Mutable.sequence, Mutable.error] at executed
    all_goals exact executed.2.symm
  | ref address =>
    cases found : heap[address]? with
    | none => simp [Mutable.sequence, found, Mutable.unsupported] at executed
    | some object =>
      cases object <;> simp [Mutable.sequence, found, Mutable.error, Mutable.unsupported] at executed
      all_goals exact executed.2.symm

theorem sequence_items_within (heap after : Heap) (closed : Closed heap) (value : Value) (items : List Value)
    (executed : Mutable.sequence value heap = some (.ok items, after)) :
    ∀ item ∈ items, item.edge.Within heap.length := by
  cases value with
  | scalar scalar =>
    cases scalar <;> simp [Mutable.sequence, Mutable.error] at executed
    all_goals
      rw [← executed.1]
      intro item member
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
      trivial
  | ref address =>
    cases found : heap[address]? with
    | none => simp [Mutable.sequence, found, Mutable.unsupported] at executed
    | some object =>
      have old := closed object (List.mem_of_getElem? found)
      cases object <;> simp [Mutable.sequence, found, Mutable.error, Mutable.unsupported] at executed
      all_goals rw [← executed.1]
      all_goals first
        | exact old
        | (intro item member; obtain ⟨_, _, rfl⟩ := List.mem_map.mp member; trivial)

variable {logical physical : Heap} {rename : Nat → Nat}

theorem integer_relocates (logical physical : Heap) (rename : Nat → Nat) (value : Value) :
    Mutable.integer (relocateValue rename value) physical =
      (Mutable.integer value logical).map (fun result => (result.1, physical)) := by
  cases value with
  | ref => rfl
  | scalar scalar => cases scalar <;> rfl

theorem integer_keeps_heap (heap after : Heap) (value : Value) (outcome : Except ExceptionObject Int)
    (executed : Mutable.integer value heap = some (outcome, after)) : after = heap := by
  have same := integer_relocates heap heap id value
  simp only [relocateValue_id, executed, Option.map_some] at same
  exact congrArg Prod.snd (Option.some.inj same)

/-- A successful list replacement retains the destination address and every surrounding alias. -/
theorem ExecutionLayout.list_update_relocates (layout : ExecutionLayout logical physical rename)
    (address : Nat) (items updated : List Value) (found : logical[address]? = some (.list items))
    (inside : ∀ value ∈ updated, value.edge.Within logical.length) (action otherAction : Eval Value)
    (first : action logical = some (.ok (.ref address), logical.set address (.list updated)))
    (second : otherAction physical =
      some (.ok (.ref (rename address)), physical.set (rename address) (.list (updated.map (relocateValue rename))))) :
    EvalRelocates logical physical rename action otherAction := by
  intro outcome after executed
  rw [first] at executed
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
  refine ⟨_, rename, ?_, layout.set_list address items updated found inside, fun _ _ => rfl, by simp, ?_⟩
  · simpa only [Except.map, relocateValue] using second
  · intro returned equal
    cases equal
    simpa only [Value.edge, Graph.Edge.Within, List.length_set] using (List.getElem?_eq_some_iff.mp found).1

theorem ExecutionLayout.inplace_mult_list (layout : ExecutionLayout logical physical rename)
    (address : Nat) (items : List Value) (count : Int) (found : logical[address]? = some (.list items)) :
    EvalRelocates logical physical rename (HeapCalls.inplace .mult (.ref address) (.scalar (.int count)))
      (HeapCalls.inplace .mult (.ref (rename address)) (.scalar (.int count))) := by
  apply layout.list_update_relocates address items _ found
    (replicated_values_within _ _ items (layout.closed _ (List.mem_of_getElem? found))) _ _
    (inplace_mult_list_eval logical address items count found)
  simpa only [map_replicated_values] using inplace_mult_list_eval physical (rename address)
    (items.map (relocateValue rename)) count (layout.runtime.lookup _ _ found)

theorem ExecutionLayout.inplace_mult_list_bool (layout : ExecutionLayout logical physical rename)
    (address : Nat) (items : List Value) (keep : Bool) (found : logical[address]? = some (.list items)) :
    EvalRelocates logical physical rename (HeapCalls.inplace .mult (.ref address) (.scalar (.bool keep)))
      (HeapCalls.inplace .mult (.ref (rename address)) (.scalar (.bool keep))) := by
  have inside : ∀ value ∈ (if keep then items else []), value.edge.Within logical.length := by
    cases keep
    · simp
    · exact layout.closed _ (List.mem_of_getElem? found)
  apply layout.list_update_relocates address items _ found inside _ _
    (inplace_mult_list_bool_eval logical address items keep found)
  have other := inplace_mult_list_bool_eval physical (rename address) (items.map (relocateValue rename)) keep
    (layout.runtime.lookup _ _ found)
  cases keep <;> simpa using other

theorem ExecutionLayout.inplace_mult_list_value (layout : ExecutionLayout logical physical rename)
    (address : Nat) (items : List Value) (right : Value) (found : logical[address]? = some (.list items)) :
    EvalRelocates logical physical rename (HeapCalls.inplace .mult (.ref address) right)
      (HeapCalls.inplace .mult (.ref (rename address)) (relocateValue rename right)) := by
  intro outcome after executed
  have source := inplace_mult_list_value_eval logical address items right found
  have target := inplace_mult_list_value_eval physical (rename address) (items.map (relocateValue rename))
    (relocateValue rename right) (layout.runtime.lookup _ _ found)
  have counts := integer_relocates logical physical rename right
  cases read : Mutable.integer right logical with
  | none => simp [source, read, Mutable.eval_bind] at executed
  | some pair =>
    rcases pair with ⟨result, middle⟩
    have same := integer_keeps_heap logical middle right result read
    subst middle
    cases result with
    | error exception =>
      have equal : Except.error exception = outcome ∧ logical = after := by
        simpa [source, read, Mutable.eval_bind] using executed
      obtain ⟨rfl, rfl⟩ := equal
      refine ⟨physical, rename, ?_, layout, fun _ _ => rfl, Nat.le_refl _, ?_⟩
      · simp [target, counts, read, Mutable.eval_bind, Except.map]
      · intro value impossible
        cases impossible
    | ok count =>
      apply layout.list_update_relocates address items _ found
        (replicated_values_within _ count.toNat items (layout.closed _ (List.mem_of_getElem? found))) _ _
        ?_ ?_ outcome after executed
      · simp [source, read, Mutable.eval_bind, Except.map]
      · simp [target, counts, read, Mutable.eval_bind, Except.map]

/-- Extension derives its result or exception without assuming the other operation completes. -/
theorem ExecutionLayout.inplace_add_list (layout : ExecutionLayout logical physical rename)
    (address : Nat) (items : List Value) (right : Value) (found : logical[address]? = some (.list items))
    (rightInside : right.edge.Within logical.length) :
    EvalRelocates logical physical rename (HeapCalls.inplace .add (.ref address) right)
      (HeapCalls.inplace .add (.ref (rename address)) (relocateValue rename right)) := by
  intro outcome after executed
  have source := inplace_add_list_eval logical address items right found
  have target := inplace_add_list_eval physical (rename address) (items.map (relocateValue rename))
    (relocateValue rename right) (layout.runtime.lookup _ _ found)
  have sequences := layout.runtime.sequence right rightInside
  cases read : Mutable.sequence right logical with
  | none => simp [source, read, Mutable.eval_bind] at executed
  | some pair =>
    rcases pair with ⟨result, middle⟩
    have same := sequence_keeps_heap logical middle right result read
    subst middle
    cases result with
    | error exception =>
      have equal : Except.error exception = outcome ∧ logical = after := by
        simpa [source, read, Mutable.eval_bind] using executed
      obtain ⟨rfl, rfl⟩ := equal
      refine ⟨physical, rename, ?_, layout, fun _ _ => rfl, Nat.le_refl _, ?_⟩
      · simp [target, sequences, read, Mutable.eval_bind, Except.map]
      · intro value impossible
        cases impossible
    | ok more =>
      have inside : ∀ value ∈ items ++ more, value.edge.Within logical.length := by
        intro value member
        rcases List.mem_append.mp member with old | new
        · exact layout.closed _ (List.mem_of_getElem? found) value old
        · exact sequence_items_within logical logical layout.closed right more read value new
      apply layout.list_update_relocates address items (items ++ more) found inside _ _ ?_ ?_ outcome after executed
      · simp [source, read, Mutable.eval_bind, Except.map]
      · simp [target, sequences, read, Mutable.eval_bind, Except.map, List.map_append]

/-- Unsupported sequence sources stay unsupported; this does not assert iterator protocol support. -/
theorem RuntimeLayout.inplace_add_list_unsupported (layout : RuntimeLayout logical physical rename)
    (address : Nat) (items : List Value) (right : Value) (found : logical[address]? = some (.list items))
    (rightInside : right.edge.Within logical.length) :
    HeapCalls.inplace .add (.ref (rename address)) (relocateValue rename right) physical = none ↔
      HeapCalls.inplace .add (.ref address) right logical = none := by
  rw [inplace_add_list_eval logical address items right found,
    inplace_add_list_eval physical (rename address) (items.map (relocateValue rename)) (relocateValue rename right)
      (layout.lookup _ _ found)]
  have sequences := layout.sequence right rightInside
  cases read : Mutable.sequence right logical with
  | none => simp [Mutable.eval_bind, sequences, read]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    cases outcome <;> simp [Mutable.eval_bind, sequences, read, Except.map]

end FormalSW.PyAst.Mutable.Relocation
