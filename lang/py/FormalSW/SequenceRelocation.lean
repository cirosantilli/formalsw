import lang.py.FormalSW.RuntimeEffects

/-! Indexed list operations retain caller aliases and execution invariants under relocation. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

/-- Index conversion depends on the sequence length and the scalar index, not allocation layout. -/
theorem index_relocates {α β : Type} (items : List α) (other : List β)
    (sameLength : other.length = items.length) (subscript : Value) (rename : Nat → Nat)
    (logical physical : Heap) :
    Mutable.index other (relocateValue rename subscript) physical =
      (Mutable.index items subscript logical).map (fun result => (result.1, physical)) := by
  cases subscript with
  | ref address => simp [Mutable.index, relocateValue, error]
  | scalar scalar =>
    cases scalar <;> simp [Mutable.index, relocateValue, sameLength, error]
    all_goals repeat' first | rfl | split

/-- Indexing either raises or returns a position within the sequence; no search bound is assumed. -/
theorem index_total {α : Type} (items : List α) (subscript : Value) (heap : Heap) :
    ∃ outcome, Mutable.index items subscript heap = some (outcome, heap) ∧
      (∀ position, outcome = .ok position → position < items.length) := by
  cases subscript with
  | ref address => simp [Mutable.index, error]
  | scalar scalar =>
    cases scalar <;> simp [Mutable.index, error]
    all_goals (repeat' split) <;> simp_all
    all_goals first | omega | exact List.length_pos_iff.mpr ‹items ≠ []›

theorem index_keeps_heap {α : Type} (items : List α) (subscript : Value)
    (heap after : Heap) (outcome : Except ExceptionObject Nat)
    (executed : Mutable.index items subscript heap = some (outcome, after)) : after = heap := by
  have same := index_relocates items items rfl subscript id heap heap
  simp only [relocateValue_id, executed, Option.map_some] at same
  exact congrArg Prod.snd (Option.some.inj same)

variable {logical physical : Heap} {rename : Nat → Nat}

theorem getElem_default_relocates (items : List Value) (position : Nat) :
    ((items.map (relocateValue rename))[position]?).getD (.scalar .none) =
      relocateValue rename ((items[position]?).getD (.scalar .none)) := by
  cases found : items[position]? <;> simp [found, relocateValue]

/-- List reads retain negative and Boolean indices, exact index errors, and shared result references. -/
theorem RuntimeLayout.getItem_list (layout : RuntimeLayout logical physical rename)
    (address : Nat) (items : List Value) (subscript : Value)
    (found : logical[address]? = some (.list items)) :
    Mutable.getItem (.ref (rename address)) (relocateValue rename subscript) physical =
      (Mutable.getItem (.ref address) subscript logical).map
        (fun result => (result.1.map (relocateValue rename), physical)) := by
  have moved := layout.lookup address _ found
  have indexed := index_relocates items (items.map (relocateValue rename)) (by simp)
    subscript rename logical physical
  cases tested : Mutable.index items subscript logical with
  | none => simp [Mutable.getItem, found, moved, relocateObject, indexed, tested, eval_bind]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have unchanged := index_keeps_heap items subscript logical after outcome tested
    subst after
    cases outcome with
    | error exception =>
      simp [Mutable.getItem, found, moved, relocateObject, indexed, tested, eval_bind, Except.map]
    | ok position =>
      simp [Mutable.getItem, found, moved, relocateObject, indexed, tested, eval_bind, Except.map]
      simpa only [List.getElem?_map] using
        (getElem_default_relocates (rename := rename) items position)

theorem RuntimeLayout.getItem_tuple (layout : RuntimeLayout logical physical rename)
    (address : Nat) (items : List Value) (subscript : Value)
    (found : logical[address]? = some (.tuple items)) :
    Mutable.getItem (.ref (rename address)) (relocateValue rename subscript) physical =
      (Mutable.getItem (.ref address) subscript logical).map
        (fun result => (result.1.map (relocateValue rename), physical)) := by
  have moved := layout.lookup address _ found
  have indexed := index_relocates items (items.map (relocateValue rename)) (by simp)
    subscript rename logical physical
  cases tested : Mutable.index items subscript logical with
  | none => simp [Mutable.getItem, found, moved, relocateObject, indexed, tested, eval_bind]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have unchanged := index_keeps_heap items subscript logical after outcome tested
    subst after
    cases outcome with
    | error exception =>
      simp [Mutable.getItem, found, moved, relocateObject, indexed, tested, eval_bind, Except.map]
    | ok position =>
      simp [Mutable.getItem, found, moved, relocateObject, indexed, tested, eval_bind, Except.map]
      simpa only [List.getElem?_map] using
        (getElem_default_relocates (rename := rename) items position)


/-- A read through a builtin sequence cannot manufacture a reference outside its heap. -/
theorem indexedRead_bounded (heap after : Heap) (items : List Value) (subscript value : Value)
    (inside : ∀ item ∈ items, item.edge.Within heap.length)
    (executed : ((fun position => (items[position]?).getD (.scalar .none)) <$>
      Mutable.index items subscript : Eval Value) heap =
        some (.ok value, after)) : value.edge.Within heap.length := by
  cases tested : Mutable.index items subscript heap with
  | none => simp [tested, Except.map] at executed
  | some pair =>
    rcases pair with ⟨result, middle⟩
    have unchanged := index_keeps_heap items subscript heap middle result tested
    subst middle
    cases result with
    | error exception => simp [tested, Except.map] at executed
    | ok position =>
      have same : (items[position]?).getD (.scalar .none) = value ∧ heap = after := by
        simpa [tested, eval_bind, Except.map] using executed
      rw [← same.1]
      cases found : items[position]? with
      | none => simp [Value.edge, Graph.Edge.Within]
      | some item => exact inside item (List.mem_of_getElem? found)

/-- Reading a list retains the full invariant for a subsequent mutation or allocation. -/
theorem ExecutionLayout.getItem_list (layout : ExecutionLayout logical physical rename)
    (address : Nat) (items : List Value) (subscript : Value)
    (found : logical[address]? = some (.list items))
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : Mutable.getItem (.ref address) subscript logical = some (outcome, after)) :
    Mutable.getItem (.ref (rename address)) (relocateValue rename subscript) physical =
        some (outcome.map (relocateValue rename), physical) ∧
      ExecutionLayout after physical rename ∧ after = logical ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length) := by
  have stationary := (RuntimeLayout.refl logical).getItem_list address items subscript found
  simp only [id_eq, relocateValue_id, executed, Option.map_some] at stationary
  have same : after = logical := congrArg Prod.snd (Option.some.inj stationary)
  subst after
  refine ⟨?_, layout, rfl, ?_⟩
  · simpa only [executed, Option.map_some] using
      layout.runtime.getItem_list address items subscript found
  · intro returned result
    subst outcome
    apply indexedRead_bounded logical logical items subscript returned
      (layout.closed _ (List.mem_of_getElem? found))
    simpa [Mutable.getItem, found, Except.map] using executed

theorem ExecutionLayout.getItem_tuple (layout : ExecutionLayout logical physical rename)
    (address : Nat) (items : List Value) (subscript : Value)
    (found : logical[address]? = some (.tuple items))
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : Mutable.getItem (.ref address) subscript logical = some (outcome, after)) :
    Mutable.getItem (.ref (rename address)) (relocateValue rename subscript) physical =
        some (outcome.map (relocateValue rename), physical) ∧
      ExecutionLayout after physical rename ∧ after = logical ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length) := by
  have stationary := (RuntimeLayout.refl logical).getItem_tuple address items subscript found
  simp only [id_eq, relocateValue_id, executed, Option.map_some] at stationary
  have same : after = logical := congrArg Prod.snd (Option.some.inj stationary)
  subst after
  refine ⟨?_, layout, rfl, ?_⟩
  · simpa only [executed, Option.map_some] using
      layout.runtime.getItem_tuple address items subscript found
  · intro returned result
    subst outcome
    apply indexedRead_bounded logical logical items subscript returned
      (layout.closed _ (List.mem_of_getElem? found))
    simpa [Mutable.getItem, found, Except.map] using executed

/-- In-place list updates retain the surrounding caller graph, closure, and tuple interning. -/
theorem ExecutionLayout.set_list (layout : ExecutionLayout logical physical rename)
    (address : Nat) (items updated : List Value)
    (found : logical[address]? = some (.list items))
    (inside : ∀ value ∈ updated, value.edge.Within logical.length) :
    ExecutionLayout (logical.set address (.list updated))
      (physical.set (rename address) (.list (updated.map (relocateValue rename)))) rename := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  refine ⟨layout.runtime.set address bound (.list updated),
    layout.closed.set address (.list updated) inside, ?_⟩
  intro index selected
  rw [emptyTupleAddress_set _ _ _ _ found (by simp) (by simp)] at selected
  rw [emptyTupleAddress_set _ _ _ _ (layout.runtime.lookup address _ found) (by simp)
    (by simp)]
  exact layout.interned index selected

/-- Successful assignment and TypeError/IndexError exits all preserve the execution relation. -/
theorem ExecutionLayout.setItem_list (layout : ExecutionLayout logical physical rename)
    (address : Nat) (items : List Value) (subscript replacement : Value)
    (found : logical[address]? = some (.list items))
    (replacementInside : replacement.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : Mutable.setItem (.ref address) subscript replacement logical = some (outcome, after)) :
    ∃ other, Mutable.setItem (.ref (rename address)) (relocateValue rename subscript)
        (relocateValue rename replacement) physical =
        some (outcome.map (relocateValue rename), other) ∧
      ExecutionLayout after other rename ∧ after.length = logical.length ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length) := by
  have moved := layout.runtime.lookup address _ found
  have indexed := index_relocates items (items.map (relocateValue rename)) (by simp)
    subscript rename logical physical
  cases tested : Mutable.index items subscript logical with
  | none => simp [Mutable.setItem, found, tested, eval_bind] at executed
  | some pair =>
    rcases pair with ⟨result, middle⟩
    have unchanged := index_keeps_heap items subscript logical middle result tested
    subst middle
    cases result with
    | error exception =>
      have result : Mutable.setItem (.ref address) subscript replacement logical =
          some (.error exception, logical) := by
        simp [Mutable.setItem, found, tested, eval_bind]
      rw [result] at executed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
      refine ⟨physical, ?_, layout, rfl, ?_⟩
      · simp [Mutable.setItem, moved, relocateObject, indexed, tested, eval_bind, Except.map]
      · intro returned impossible
        cases impossible
    | ok position =>
      have result : Mutable.setItem (.ref address) subscript replacement logical =
          some (.ok (.scalar .none), logical.set address (.list (items.set position replacement))) := by
        simp [Mutable.setItem, found, tested, eval_bind, Except.map]
      rw [result] at executed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
      have old := layout.closed _ (List.mem_of_getElem? found)
      have inside : ∀ value ∈ items.set position replacement, value.edge.Within logical.length := by
        intro value member
        rcases List.mem_or_eq_of_mem_set member with original | equal
        · exact old value original
        · simpa only [equal] using replacementInside
      refine ⟨physical.set (rename address)
        (.list ((items.set position replacement).map (relocateValue rename))), ?_,
        layout.set_list address items _ found inside, by simp, ?_⟩
      · change Mutable.setItem (.ref (rename address)) (relocateValue rename subscript)
          (relocateValue rename replacement) physical = some (.ok (.scalar .none), _)
        simp [Mutable.setItem, moved, relocateObject, indexed, tested, eval_bind,
          Except.map, List.map_set]
      · intro returned same
        have equal : returned = .scalar .none := by simpa using same.symm
        simp [equal, Value.edge, Graph.Edge.Within]

/-- Append preserves aliases, including a list's reference to itself. -/
theorem ExecutionLayout.appendItem_list (layout : ExecutionLayout logical physical rename)
    (address : Nat) (items : List Value) (value : Value)
    (found : logical[address]? = some (.list items))
    (inside : value.edge.Within logical.length) :
    let after := logical.set address (.list (items ++ [value]))
    let other := physical.set (rename address)
      (.list ((items ++ [value]).map (relocateValue rename)))
    Mutable.appendItem address value logical = some (.ok (.scalar .none), after) ∧
      Mutable.appendItem (rename address) (relocateValue rename value) physical =
        some (.ok (.scalar .none), other) ∧
      ExecutionLayout after other rename := by
  have old := layout.closed _ (List.mem_of_getElem? found)
  refine ⟨by simp [Mutable.appendItem, found, Except.map], ?_, layout.set_list address items _ found ?_⟩
  · simp [Mutable.appendItem, layout.runtime.lookup address _ found, relocateObject, Except.map]
  · intro item member
    rcases List.mem_append.mp member with previous | added
    · exact old item previous
    · simpa only [List.mem_singleton.mp added] using inside

end FormalSW.PyAst.Mutable.Relocation
