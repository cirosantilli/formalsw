import lang.py.FormalSW.KeyRelocation

/-! Dictionary updates preserve stored representatives, aliases, and execution invariants. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

/-- Replacing a nonempty-tuple object by another cannot change empty-tuple interning. -/
theorem ExecutionLayout.set_nonempty {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (address : Nat) (old updated : Object)
    (found : logical[address]? = some old) (oldNotEmpty : old ≠ .tuple [])
    (newNotEmpty : updated ≠ .tuple []) (inside : ObjectWithin logical.length updated) :
    ExecutionLayout (logical.set address updated)
      (physical.set (rename address) (relocateObject rename updated)) rename := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  refine ⟨layout.runtime.set address bound updated, layout.closed.set address updated inside, ?_⟩
  intro index selected
  rw [emptyTupleAddress_set _ _ _ _ found oldNotEmpty newNotEmpty] at selected
  rw [emptyTupleAddress_set _ _ _ _ (layout.runtime.lookup address _ found)
    (by simpa using oldNotEmpty) (by simpa using newNotEmpty)]
  exact layout.interned index selected

def relocateHashEntries (rename : Nat → Nat) (entries : List (HashDict.Entry Value)) :=
  entries.map fun entry => (entry.1, relocateValue rename entry.2.1, relocateValue rename entry.2.2)

theorem hashDict_insert_relocates (entries : List (HashDict.Entry Value)) (rename : Nat → Nat)
    (key : HashKey) (representative value : Value) :
    relocateHashEntries rename (HashDict.insert entries key representative value) =
      HashDict.insert (relocateHashEntries rename entries) key
        (relocateValue rename representative) (relocateValue rename value) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [relocateHashEntries] at ih ⊢
    cases compared : HashKey.equal entry.1 key <;> simp [HashDict.insert, compared, ih]

theorem hashDict_insert_within (entries : List (HashDict.Entry Value)) (key : HashKey)
    (representative value : Value) (limit : Nat)
    (old : ∀ entry ∈ entries, entry.2.1.edge.Within limit ∧ entry.2.2.edge.Within limit)
    (representativeInside : representative.edge.Within limit) (valueInside : value.edge.Within limit) :
    ∀ entry ∈ HashDict.insert entries key representative value,
      entry.2.1.edge.Within limit ∧ entry.2.2.edge.Within limit := by
  induction entries with
  | nil => simpa [HashDict.insert] using And.intro representativeInside valueInside
  | cons entry rest ih =>
    have head := old entry (by simp)
    have tail : ∀ entry ∈ rest, entry.2.1.edge.Within limit ∧ entry.2.2.edge.Within limit := by
      intro entry member
      exact old entry (by simp [member])
    simp only [HashDict.insert]
    split
    · simpa using And.intro (And.intro head.1 valueInside) tail
    · simpa using And.intro head (ih tail)

theorem ObjectWithin.keyDict_insert (entries : List (HashDict.Entry Value)) (key : HashKey)
    (representative value : Value) (limit : Nat) (old : ObjectWithin limit (.keyDict entries))
    (representativeInside : representative.edge.Within limit) (valueInside : value.edge.Within limit) :
    ObjectWithin limit (.keyDict (HashDict.insert entries key representative value)) := by
  have entriesInside : ∀ entry ∈ entries, entry.2.1.edge.Within limit ∧ entry.2.2.edge.Within limit := by
    intro entry member
    exact ⟨old entry.2.1 (List.mem_flatMap.mpr ⟨entry, member, by simp⟩),
      old entry.2.2 (List.mem_flatMap.mpr ⟨entry, member, by simp⟩)⟩
  have updated := hashDict_insert_within entries key representative value limit
    entriesInside representativeInside valueInside
  intro stored member
  obtain ⟨entry, present, belongs⟩ := List.mem_flatMap.mp member
  have selected : stored = entry.2.1 ∨ stored = entry.2.2 := by simpa using belongs
  rcases selected with rfl | rfl
  · exact (updated entry present).1
  · exact (updated entry present).2

theorem scalarDict_insert_relocates (entries : List (Constant × Value)) (rename : Nat → Nat)
    (key : Constant) (value : Value) :
    (ScalarDict.insert entries key value).map (fun entry => (entry.1, relocateValue rename entry.2)) =
      ScalarDict.insert (entries.map fun entry => (entry.1, relocateValue rename entry.2))
        key (relocateValue rename value) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨stored, previous⟩
    cases compared : (scalarCompare .eq stored key).getD false <;> simp [ScalarDict.insert, compared, ih]

theorem ObjectWithin.dict_insert (entries : List (Constant × Value)) (key : Constant)
    (value : Value) (limit : Nat) (old : ObjectWithin limit (.dict entries))
    (inside : value.edge.Within limit) :
    ObjectWithin limit (.dict (ScalarDict.insert entries key value)) := by
  have updated := ScalarDict.insert_property entries key value (fun _ => True)
    (fun stored => stored.edge.Within limit)
    (fun entry member => ⟨trivial, old entry.2 (List.mem_map.mpr ⟨entry, member, rfl⟩)⟩) trivial inside
  intro stored member
  obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
  exact (updated entry present).2

theorem promoteDictionary_relocates (entries : List (Constant × Value)) (rename : Nat → Nat) :
    Mutable.promoteDictionary (entries.map fun entry => (entry.1, relocateValue rename entry.2)) =
      relocateHashEntries rename (Mutable.promoteDictionary entries) := by
  simp [Mutable.promoteDictionary, relocateHashEntries, relocateValue, List.map_map, Function.comp_def]

theorem ObjectWithin.promoteDictionary (entries : List (Constant × Value)) (limit : Nat)
    (old : ObjectWithin limit (.dict entries)) :
    ObjectWithin limit (.keyDict (Mutable.promoteDictionary entries)) := by
  intro stored member
  obtain ⟨entry, present, belongs⟩ := List.mem_flatMap.mp member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp present
  have selected : stored = .scalar original.1 ∨ stored = original.2 := by simpa using belongs
  rcases selected with rfl | rfl
  · simp [Value.edge, Graph.Edge.Within]
  · exact old original.2 (List.mem_map.mpr ⟨original, originalMember, rfl⟩)

variable {logical physical : Heap} {rename : Nat → Nat}

/-- Tuple-key dictionary writes retain the execution invariant on both success and hashing errors. -/
theorem ExecutionLayout.setItem_keyDict (layout : ExecutionLayout logical physical rename)
    (address : Nat) (entries : List (HashDict.Entry Value)) (subscript replacement : Value)
    (found : logical[address]? = some (.keyDict entries))
    (keyInside : subscript.edge.Within logical.length)
    (replacementInside : replacement.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : Mutable.setItem (.ref address) subscript replacement logical = some (outcome, after)) :
    ∃ other, Mutable.setItem (.ref (rename address)) (relocateValue rename subscript)
        (relocateValue rename replacement) physical =
        some (outcome.map (relocateValue rename), other) ∧
      ExecutionLayout after other rename ∧ after.length = logical.length ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length) := by
  have moved := layout.runtime.lookup address _ found
  have same := layout.runtime.keyOf layout.closed subscript keyInside
  cases resolved : Mutable.keyOf logical subscript with
  | none => simp [Mutable.setItem, found, Mutable.hashKey, resolved, eval_bind] at executed
  | some result =>
    cases result with
    | error exception =>
      have result : Mutable.setItem (.ref address) subscript replacement logical =
          some (.error exception, logical) := by
        simp [Mutable.setItem, found, Mutable.hashKey, resolved, eval_bind]
      rw [result] at executed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
      refine ⟨physical, ?_, layout, rfl, ?_⟩
      · simp [Mutable.setItem, moved, relocateObject, Mutable.hashKey, same, resolved, eval_bind, Except.map]
      · intro returned impossible
        cases impossible
    | ok key =>
      have result : Mutable.setItem (.ref address) subscript replacement logical =
          some (.ok (.scalar .none), logical.set address
            (.keyDict (HashDict.insert entries key subscript replacement))) := by
        simp [Mutable.setItem, found, Mutable.hashKey, resolved, eval_bind, Except.map]
      rw [result] at executed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
      have inside := ObjectWithin.keyDict_insert entries key subscript replacement logical.length
        (layout.closed _ (List.mem_of_getElem? found)) keyInside replacementInside
      have retained := layout.set_nonempty address _ _ found (by simp) (by simp) inside
      have inserted := hashDict_insert_relocates entries rename key subscript replacement
      simp only [relocateHashEntries] at inserted
      refine ⟨physical.set (rename address)
        (relocateObject rename (.keyDict (HashDict.insert entries key subscript replacement))),
        ?_, retained, by simp, ?_⟩
      · change Mutable.setItem (.ref (rename address)) (relocateValue rename subscript)
          (relocateValue rename replacement) physical = some (.ok (.scalar .none), _)
        simp [Mutable.setItem, moved, relocateObject, Mutable.hashKey, same, resolved,
          eval_bind, Except.map, inserted]
      · intro returned equal
        have value : returned = .scalar .none := by simpa using equal.symm
        simp [value, Value.edge, Graph.Edge.Within]

/-- Scalar updates retain the dictionary form; reference keys promote it without copying values. -/
theorem ExecutionLayout.setItem_dict (layout : ExecutionLayout logical physical rename)
    (address : Nat) (entries : List (Constant × Value)) (subscript replacement : Value)
    (found : logical[address]? = some (.dict entries))
    (keyInside : subscript.edge.Within logical.length)
    (replacementInside : replacement.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : Mutable.setItem (.ref address) subscript replacement logical = some (outcome, after)) :
    ∃ other, Mutable.setItem (.ref (rename address)) (relocateValue rename subscript)
        (relocateValue rename replacement) physical =
        some (outcome.map (relocateValue rename), other) ∧
      ExecutionLayout after other rename ∧ after.length = logical.length ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length) := by
  have moved := layout.runtime.lookup address _ found
  have old := layout.closed _ (List.mem_of_getElem? found)
  cases subscript with
  | scalar key =>
    have result : Mutable.setItem (.ref address) (.scalar key) replacement logical =
        some (.ok (.scalar .none), logical.set address (.dict (ScalarDict.insert entries key replacement))) := by
      simp [Mutable.setItem, found, Except.map]
    rw [result] at executed
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
    have inside := ObjectWithin.dict_insert entries key replacement logical.length old replacementInside
    have retained := layout.set_nonempty address _ _ found (by simp) (by simp) inside
    refine ⟨physical.set (rename address)
      (relocateObject rename (.dict (ScalarDict.insert entries key replacement))), ?_, retained, by simp, ?_⟩
    · change Mutable.setItem (.ref (rename address)) (.scalar key)
        (relocateValue rename replacement) physical = some (.ok (.scalar .none), _)
      simp [Mutable.setItem, moved, relocateObject, Except.map, scalarDict_insert_relocates]
    · intro returned equal
      have value : returned = .scalar .none := by simpa using equal.symm
      simp [value, Value.edge, Graph.Edge.Within]
  | ref keyAddress =>
    have same := layout.runtime.keyOf layout.closed (.ref keyAddress) keyInside
    cases resolved : Mutable.keyOf logical (.ref keyAddress) with
    | none => simp [Mutable.setItem, found, Mutable.hashKey, resolved, eval_bind] at executed
    | some result =>
      cases result with
      | error exception =>
        have result : Mutable.setItem (.ref address) (.ref keyAddress) replacement logical =
            some (.error exception, logical) := by
          simp [Mutable.setItem, found, Mutable.hashKey, resolved, eval_bind]
        rw [result] at executed
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
        refine ⟨physical, ?_, layout, rfl, ?_⟩
        · simp only [relocateValue] at same ⊢
          simp [Mutable.setItem, moved, relocateObject, Mutable.hashKey, same, resolved, eval_bind, Except.map]
        · intro returned impossible
          cases impossible
      | ok key =>
        have result : Mutable.setItem (.ref address) (.ref keyAddress) replacement logical =
            some (.ok (.scalar .none), logical.set address (.keyDict
              (HashDict.insert (Mutable.promoteDictionary entries) key (.ref keyAddress) replacement))) := by
          simp [Mutable.setItem, found, Mutable.hashKey, resolved, eval_bind, Except.map]
        rw [result] at executed
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
        have inside := ObjectWithin.keyDict_insert (Mutable.promoteDictionary entries) key
          (.ref keyAddress) replacement logical.length (old.promoteDictionary entries logical.length)
          keyInside replacementInside
        have retained := layout.set_nonempty address _ _ found (by simp) (by simp) inside
        have inserted := hashDict_insert_relocates (Mutable.promoteDictionary entries) rename key
          (.ref keyAddress) replacement
        have promoted := promoteDictionary_relocates entries rename
        have refSame : relocateValue rename (.ref keyAddress) = .ref (rename keyAddress) := rfl
        simp only [relocateHashEntries, refSame] at inserted promoted same
        refine ⟨physical.set (rename address) (relocateObject rename (.keyDict
          (HashDict.insert (Mutable.promoteDictionary entries) key (.ref keyAddress) replacement))),
          ?_, retained, by simp, ?_⟩
        · change Mutable.setItem (.ref (rename address)) (.ref (rename keyAddress))
            (relocateValue rename replacement) physical = some (.ok (.scalar .none), _)
          simp [Mutable.setItem, moved, relocateObject, Mutable.hashKey, same, resolved,
            eval_bind, Except.map, inserted, promoted]
        · intro returned equal
          have value : returned = .scalar .none := by simpa using equal.symm
          simp [value, Value.edge, Graph.Edge.Within]

theorem RuntimeLayout.setItem_keyDict_unsupported (layout : RuntimeLayout logical physical rename)
    (closed : Closed logical) (address : Nat) (entries : List (HashDict.Entry Value))
    (subscript replacement : Value) (found : logical[address]? = some (.keyDict entries))
    (inside : subscript.edge.Within logical.length) :
    Mutable.setItem (.ref (rename address)) (relocateValue rename subscript)
        (relocateValue rename replacement) physical = none ↔
      Mutable.setItem (.ref address) subscript replacement logical = none := by
  have moved := layout.lookup address _ found
  have same := layout.keyOf closed subscript inside
  cases resolved : Mutable.keyOf logical subscript with
  | none => simp [Mutable.setItem, found, moved, relocateObject, Mutable.hashKey, same, resolved, eval_bind]
  | some outcome =>
    cases outcome <;> simp [Mutable.setItem, found, moved, relocateObject, Mutable.hashKey,
      same, resolved, eval_bind, Except.map]

theorem RuntimeLayout.setItem_dict_unsupported (layout : RuntimeLayout logical physical rename)
    (closed : Closed logical) (address : Nat) (entries : List (Constant × Value))
    (subscript replacement : Value) (found : logical[address]? = some (.dict entries))
    (inside : subscript.edge.Within logical.length) :
    Mutable.setItem (.ref (rename address)) (relocateValue rename subscript)
        (relocateValue rename replacement) physical = none ↔
      Mutable.setItem (.ref address) subscript replacement logical = none := by
  have moved := layout.lookup address _ found
  cases subscript with
  | scalar key => simp [Mutable.setItem, found, moved, relocateObject, relocateValue, Except.map]
  | ref keyAddress =>
    have same := layout.keyOf closed (.ref keyAddress) inside
    simp only [relocateValue] at same ⊢
    cases resolved : Mutable.keyOf logical (.ref keyAddress) with
    | none => simp [Mutable.setItem, found, moved, relocateObject, Mutable.hashKey, same, resolved, eval_bind]
    | some outcome =>
      cases outcome <;> simp [Mutable.setItem, found, moved, relocateObject, Mutable.hashKey,
        same, resolved, eval_bind, Except.map]

theorem scalarDict_lookup_relocates (entries : List (Constant × Value)) (rename : Nat → Nat)
    (key : Constant) :
    ScalarDict.lookup (entries.map fun entry => (entry.1, relocateValue rename entry.2)) key =
      (ScalarDict.lookup entries key).map (relocateValue rename) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨stored, previous⟩
    cases compared : (scalarCompare .eq stored key).getD false <;> simp [ScalarDict.lookup, compared, ih]

/-- Both scalar lookup and tuple-key lookup through a promoted view retain their actual outcomes. -/
theorem RuntimeLayout.getItem_dict (layout : RuntimeLayout logical physical rename)
    (closed : Closed logical) (address : Nat) (entries : List (Constant × Value))
    (subscript : Value) (found : logical[address]? = some (.dict entries))
    (inside : subscript.edge.Within logical.length) :
    Mutable.getItem (.ref (rename address)) (relocateValue rename subscript) physical =
      (Mutable.getItem (.ref address) subscript logical).map
        (fun result => (result.1.map (relocateValue rename), physical)) := by
  have moved := layout.lookup address _ found
  cases subscript with
  | scalar key =>
    change Mutable.getItem (.ref (rename address)) (.scalar key) physical = _
    have lookup := scalarDict_lookup_relocates entries rename key
    cases selected : ScalarDict.lookup entries key <;>
      simp [Mutable.getItem, found, moved, relocateObject, lookup, selected, Except.map]
  | ref keyAddress =>
    change Mutable.getItem (.ref (rename address)) (.ref (rename keyAddress)) physical = _
    have same := layout.keyOf closed (.ref keyAddress) inside
    simp only [relocateValue] at same
    have promoted := promoteDictionary_relocates entries rename
    simp only [relocateHashEntries] at promoted
    cases resolved : Mutable.keyOf logical (.ref keyAddress) with
    | none => simp [Mutable.getItem, found, moved, relocateObject, Mutable.hashKey, same, resolved, eval_bind]
    | some outcome =>
      cases outcome with
      | error exception =>
        simp [Mutable.getItem, found, moved, relocateObject, Mutable.hashKey, same, resolved,
          eval_bind, Except.map]
      | ok key =>
        have lookup := hashDict_lookup_relocates (Mutable.promoteDictionary entries) rename key
        cases selected : HashDict.lookup (Mutable.promoteDictionary entries) key with
        | some value =>
          simp [Mutable.getItem, found, moved, relocateObject, Mutable.hashKey, same, resolved,
            eval_bind, promoted, lookup, selected, Except.map]
        | none =>
          simp [Mutable.getItem, found, moved, relocateObject, Mutable.hashKey, same, resolved,
            eval_bind, promoted, lookup, selected]
          rfl

theorem getItem_dict_bounded (heap after : Heap) (closed : Closed heap) (address : Nat)
    (entries : List (Constant × Value)) (subscript value : Value)
    (found : heap[address]? = some (.dict entries))
    (executed : Mutable.getItem (.ref address) subscript heap = some (.ok value, after)) :
    value.edge.Within heap.length := by
  have old := closed _ (List.mem_of_getElem? found)
  cases subscript with
  | scalar key =>
    cases selected : ScalarDict.lookup entries key with
    | none => simp [Mutable.getItem, found, selected] at executed
    | some stored =>
      have result : stored = value ∧ heap = after := by
        simpa [Mutable.getItem, found, selected] using executed
      rw [← result.1]
      exact ScalarDict.lookup_property entries key (fun item => item.edge.Within heap.length)
        (fun entry member => old entry.2 (List.mem_map.mpr ⟨entry, member, rfl⟩)) selected
  | ref keyAddress =>
    have promoted := ObjectWithin.promoteDictionary entries heap.length old
    cases resolved : Mutable.keyOf heap (.ref keyAddress) with
    | none => simp [Mutable.getItem, found, Mutable.hashKey, resolved, eval_bind] at executed
    | some outcome =>
      cases outcome with
      | error exception => simp [Mutable.getItem, found, Mutable.hashKey, resolved, eval_bind] at executed
      | ok key =>
        cases selected : HashDict.find? (Mutable.promoteDictionary entries) key with
        | none =>
          simp [Mutable.getItem, found, Mutable.hashKey, resolved, eval_bind,
            HashDict.lookup, selected] at executed
          cases executed
        | some entry =>
          have result : entry.2.2 = value ∧ heap = after := by
            simpa [Mutable.getItem, found, Mutable.hashKey, resolved, eval_bind,
              HashDict.lookup, selected] using executed
          rw [← result.1]
          have member := List.mem_of_find?_eq_some selected
          exact promoted entry.2.2 (List.mem_flatMap.mpr ⟨entry, member, by simp⟩)

theorem ExecutionLayout.getItem_dict (layout : ExecutionLayout logical physical rename)
    (address : Nat) (entries : List (Constant × Value)) (subscript : Value)
    (found : logical[address]? = some (.dict entries)) (inside : subscript.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : Mutable.getItem (.ref address) subscript logical = some (outcome, after)) :
    Mutable.getItem (.ref (rename address)) (relocateValue rename subscript) physical =
        some (outcome.map (relocateValue rename), physical) ∧
      ExecutionLayout after physical rename ∧ after = logical ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length) := by
  have stationary := (RuntimeLayout.refl logical).getItem_dict layout.closed address entries subscript found inside
  simp only [id_eq, relocateValue_id, executed, Option.map_some] at stationary
  have unchanged : after = logical := congrArg Prod.snd (Option.some.inj stationary)
  subst after
  refine ⟨?_, layout, rfl, ?_⟩
  · simpa only [executed, Option.map_some] using
      layout.runtime.getItem_dict layout.closed address entries subscript found inside
  · intro returned result
    subst outcome
    exact getItem_dict_bounded logical logical layout.closed address entries subscript returned found executed

end FormalSW.PyAst.Mutable.Relocation
