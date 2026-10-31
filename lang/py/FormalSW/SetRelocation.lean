import lang.py.FormalSW.DictionaryRelocation

/-! Set insertion and hashed membership retain aliases across allocation layouts. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

variable {logical physical : Heap} {rename : Nat → Nat}

def relocateKeyEntries (rename : Nat → Nat) (items : List (HashKey × Value)) :=
  items.map fun entry => (entry.1, relocateValue rename entry.2)

theorem keyContains_relocates (items : List (HashKey × Value)) (rename : Nat → Nat) (key : HashKey) :
    Mutable.keyContains (relocateKeyEntries rename items) key = Mutable.keyContains items key := by
  simp [Mutable.keyContains, relocateKeyEntries, List.any_map, Function.comp_def]

theorem insertKey_relocates (items : List (HashKey × Value)) (rename : Nat → Nat)
    (key : HashKey) (value : Value) :
    relocateKeyEntries rename (Mutable.insertKey items (key, value)) =
      Mutable.insertKey (relocateKeyEntries rename items) (key, relocateValue rename value) := by
  simp only [Mutable.insertKey, keyContains_relocates]
  split <;> simp [relocateKeyEntries]

theorem ObjectWithin.keySet_insert (items : List (HashKey × Value)) (key : HashKey) (value : Value)
    (limit : Nat) (old : ObjectWithin limit (.keySet items)) (inside : value.edge.Within limit) :
    ObjectWithin limit (.keySet (Mutable.insertKey items (key, value))) := by
  simp only [Mutable.insertKey]
  split
  · exact old
  · intro stored member
    obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    rcases List.mem_append.mp present with previous | added
    · exact old entry.2 (List.mem_map.mpr ⟨entry, previous, rfl⟩)
    · simpa only [List.mem_singleton.mp added] using inside

theorem promotedSet_within (items : List Constant) (limit : Nat) :
    ObjectWithin limit (.keySet (items.map fun item => (HashKey.scalar item, Value.scalar item))) := by
  intro stored member
  obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨item, _, rfl⟩ := List.mem_map.mp present
  simp [Value.edge, Graph.Edge.Within]

theorem promotedSet_relocates (items : List Constant) (rename : Nat → Nat) :
    relocateKeyEntries rename (items.map fun item => (HashKey.scalar item, Value.scalar item)) =
      items.map (fun item => (HashKey.scalar item, Value.scalar item)) := by
  simp [relocateKeyEntries, relocateValue, List.map_map, Function.comp_def]

/-- Receiver binding captures the same relocated set before argument evaluation. -/
theorem RuntimeLayout.addReceiver (layout : RuntimeLayout logical physical rename) (value : Value)
    (inside : value.edge.Within logical.length) :
    Mutable.addReceiver (relocateValue rename value) physical =
      (Mutable.addReceiver value logical).map (fun result => (result.1.map rename, physical)) := by
  cases value with
  | scalar scalar => simp [Mutable.addReceiver, relocateValue, error, Except.map]
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    cases object : logical[address] <;>
      simp only [object, relocateObject] at moved <;>
      simp [Mutable.addReceiver, relocateValue, found, object, moved, error, Except.map]

/-- Every supported add result preserves the full execution relation, including errors. -/
theorem ExecutionLayout.addItem (layout : ExecutionLayout logical physical rename)
    (address : Nat) (value : Value) (addressInside : address < logical.length)
    (inside : value.edge.Within logical.length) (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : Mutable.addItem address value logical = some (outcome, after)) :
    ∃ other, Mutable.addItem (rename address) (relocateValue rename value) physical =
        some (outcome.map (relocateValue rename), other) ∧
      ExecutionLayout after other rename ∧ after.length = logical.length ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length) := by
  have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem addressInside
  generalize objectValue : logical[address] = object at found
  have moved := layout.runtime.lookup address _ found
  have old := layout.closed _ (List.mem_of_getElem? found)
  cases object with
  | keySet items =>
    have same := layout.runtime.keyOf layout.closed value inside
    cases resolved : Mutable.keyOf logical value with
    | none => simp [Mutable.addItem, found, Mutable.hashKey, resolved, eval_bind] at executed
    | some result =>
      cases result with
      | error exception =>
        have result : Mutable.addItem address value logical = some (.error exception, logical) := by
          simp [Mutable.addItem, found, Mutable.hashKey, resolved, eval_bind]
        rw [result] at executed
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
        refine ⟨physical, ?_, layout, rfl, ?_⟩
        · simp [Mutable.addItem, moved, relocateObject, Mutable.hashKey, same, resolved, eval_bind, Except.map]
        · intro returned impossible
          cases impossible
      | ok key =>
        have result : Mutable.addItem address value logical =
            some (.ok (.scalar .none), logical.set address (.keySet (Mutable.insertKey items (key, value)))) := by
          simp [Mutable.addItem, found, Mutable.hashKey, resolved, eval_bind, Except.map]
        rw [result] at executed
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
        have retained := layout.set_nonempty address _ _ found (by simp) (by simp)
          (ObjectWithin.keySet_insert items key value logical.length old inside)
        have inserted := insertKey_relocates items rename key value
        simp only [relocateKeyEntries] at inserted
        refine ⟨physical.set (rename address) (relocateObject rename
          (.keySet (Mutable.insertKey items (key, value)))), ?_, retained, by simp, ?_⟩
        · change Mutable.addItem (rename address) (relocateValue rename value) physical =
            some (.ok (.scalar .none), _)
          simp [Mutable.addItem, moved, relocateObject, Mutable.hashKey, same, resolved,
            eval_bind, Except.map, inserted]
        · intro returned equal
          have result : returned = .scalar .none := by simpa using equal.symm
          simp [result, Value.edge, Graph.Edge.Within]
  | set items =>
    cases value with
    | scalar scalar =>
      have result : Mutable.addItem address (.scalar scalar) logical =
          some (.ok (.scalar .none), logical.set address (.set (ScalarSet.insert items scalar))) := by
        simp [Mutable.addItem, found, Except.map]
      rw [result] at executed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
      refine ⟨physical.set (rename address) (.set (ScalarSet.insert items scalar)), ?_,
        layout.set_nonempty address _ _ found (by simp) (by simp) (by simp [ObjectWithin, objectValues]),
        by simp, ?_⟩
      · simp [Mutable.addItem, moved, relocateObject, relocateValue, Except.map]
      · intro returned equal
        have result : returned = .scalar .none := by simpa using equal.symm
        simp [result, Value.edge, Graph.Edge.Within]
    | ref keyAddress =>
      have same := layout.runtime.keyOf layout.closed (.ref keyAddress) inside
      simp only [relocateValue] at same
      cases resolved : Mutable.keyOf logical (.ref keyAddress) with
      | none => simp [Mutable.addItem, found, Mutable.hashKey, resolved, eval_bind] at executed
      | some result =>
        cases result with
        | error exception =>
          have result : Mutable.addItem address (.ref keyAddress) logical = some (.error exception, logical) := by
            simp [Mutable.addItem, found, Mutable.hashKey, resolved, eval_bind]
          rw [result] at executed
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
          refine ⟨physical, ?_, layout, rfl, ?_⟩
          · simp [Mutable.addItem, moved, relocateObject, relocateValue, Mutable.hashKey, same, resolved,
              eval_bind, Except.map]
          · intro returned impossible
            cases impossible
        | ok key =>
          let promoted := items.map (fun item => (HashKey.scalar item, Value.scalar item))
          have result : Mutable.addItem address (.ref keyAddress) logical =
              some (.ok (.scalar .none), logical.set address
                (.keySet (Mutable.insertKey promoted (key, .ref keyAddress)))) := by
            simp [Mutable.addItem, found, Mutable.hashKey, resolved, eval_bind, Except.map, promoted]
          rw [result] at executed
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
          have retained := layout.set_nonempty address _ _ found (by simp) (by simp)
            (ObjectWithin.keySet_insert promoted key (.ref keyAddress) logical.length
              (promotedSet_within items logical.length) inside)
          have inserted := insertKey_relocates promoted rename key (.ref keyAddress)
          have promotion := promotedSet_relocates items rename
          have refSame : relocateValue rename (.ref keyAddress) = .ref (rename keyAddress) := rfl
          simp only [refSame, promoted, promotion] at inserted
          simp only [relocateKeyEntries] at inserted
          refine ⟨physical.set (rename address) (relocateObject rename
            (.keySet (Mutable.insertKey promoted (key, .ref keyAddress)))), ?_, retained, by simp, ?_⟩
          · change Mutable.addItem (rename address) (.ref (rename keyAddress)) physical =
              some (.ok (.scalar .none), _)
            simp [Mutable.addItem, moved, relocateObject, Mutable.hashKey, same, resolved,
              eval_bind, Except.map, promoted, inserted]
          · intro returned equal
            have result : returned = .scalar .none := by simpa using equal.symm
            simp [result, Value.edge, Graph.Edge.Within]
  | list items | tuple items | bytearray bytes | dict entries | keyDict entries
  | «instance» origin name fields | dataInstance origin name frozen declared fields =>
    have result : Mutable.addItem address value logical =
        some (.error {typeName := "AttributeError", args := []}, logical) := by
      simp [Mutable.addItem, found, error]
    rw [result] at executed
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
    refine ⟨physical, ?_, layout, rfl, ?_⟩
    · simp [Mutable.addItem, moved, relocateObject, error, Except.map]
    · intro returned impossible
      cases impossible

theorem RuntimeLayout.addItem_unsupported (layout : RuntimeLayout logical physical rename)
    (closed : Closed logical) (address : Nat) (value : Value)
    (addressInside : address < logical.length) (inside : value.edge.Within logical.length) :
    Mutable.addItem (rename address) (relocateValue rename value) physical = none ↔
      Mutable.addItem address value logical = none := by
  have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem addressInside
  generalize objectValue : logical[address] = object at found
  have moved := layout.lookup address _ found
  have same := layout.keyOf closed value inside
  cases object with
  | keySet items =>
    cases resolved : Mutable.keyOf logical value with
    | none => simp [Mutable.addItem, found, moved, relocateObject, Mutable.hashKey, same, resolved, eval_bind]
    | some outcome =>
      cases outcome <;> simp [Mutable.addItem, found, moved, relocateObject, Mutable.hashKey,
        same, resolved, eval_bind, Except.map]
  | set items =>
    cases value with
    | scalar scalar => simp [Mutable.addItem, found, moved, relocateObject, relocateValue, Except.map]
    | ref address =>
      simp only [relocateValue] at same ⊢
      cases resolved : Mutable.keyOf logical (.ref address) with
      | none => simp [Mutable.addItem, found, moved, relocateObject, Mutable.hashKey, same, resolved, eval_bind]
      | some outcome =>
        cases outcome <;> simp [Mutable.addItem, found, moved, relocateObject, Mutable.hashKey,
          same, resolved, eval_bind, Except.map]
  | list items | tuple items | bytearray bytes | dict entries | keyDict entries
  | «instance» origin name fields | dataInstance origin name frozen declared fields =>
    simp [Mutable.addItem, found, moved, relocateObject, error]

/-- Mutable-set membership needles retain their unsupported protocol boundary. -/
theorem RuntimeLayout.membershipKey (layout : RuntimeLayout logical physical rename)
    (closed : Closed logical) (needle : Value) (inside : needle.edge.Within logical.length) :
    HeapCalls.membershipKey (relocateValue rename needle) physical =
      (HeapCalls.membershipKey needle logical).map (fun result => (result.1, physical)) := by
  have same := layout.keyOf closed needle inside
  cases needle with
  | scalar scalar => simp [HeapCalls.membershipKey, relocateValue, Mutable.hashKey, Mutable.keyOf, Mutable.keyOfFuel]
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    simp only [relocateValue] at same ⊢
    cases object : logical[address] <;>
      simp only [object, relocateObject] at moved <;>
      simp [HeapCalls.membershipKey, found, object, moved, Mutable.hashKey, same,
        unsupported, Option.map_map, Function.comp_def]

theorem membershipKey_keeps_heap (heap after : Heap) (closed : Closed heap) (needle : Value)
    (inside : needle.edge.Within heap.length) (outcome : Except ExceptionObject HashKey)
    (executed : HeapCalls.membershipKey needle heap = some (outcome, after)) : after = heap := by
  have same := (RuntimeLayout.refl heap).membershipKey closed needle inside
  simp only [relocateValue_id, executed, Option.map_some] at same
  exact congrArg Prod.snd (Option.some.inj same)

theorem RuntimeLayout.membership_keySet (layout : RuntimeLayout logical physical rename)
    (closed : Closed logical) (address : Nat) (items : List (HashKey × Value)) (needle : Value)
    (negated : Bool) (found : logical[address]? = some (.keySet items))
    (inside : needle.edge.Within logical.length) :
    HeapCalls.membership (relocateValue rename needle) (.ref (rename address)) negated physical =
      (HeapCalls.membership needle (.ref address) negated logical).map
        (fun result => (result.1.map (relocateValue rename), physical)) := by
  have moved := layout.lookup address _ found
  have queried := layout.membershipKey closed needle inside
  have contains := keyContains_relocates items rename
  simp only [relocateKeyEntries] at contains
  cases query : HeapCalls.membershipKey needle logical with
  | none => simp [HeapCalls.membership, found, moved, relocateObject, queried, query, eval_bind]
  | some pair =>
    rcases pair with ⟨outcome, after⟩
    have unchanged := membershipKey_keeps_heap logical after closed needle inside outcome query
    subst after
    cases outcome <;> simp [HeapCalls.membership, found, moved, relocateObject,
      queried, query, eval_bind, contains, Except.map]
    rfl

theorem RuntimeLayout.membership_set (layout : RuntimeLayout logical physical rename)
    (closed : Closed logical) (address : Nat) (items : List Constant) (needle : Value)
    (negated : Bool) (found : logical[address]? = some (.set items))
    (inside : needle.edge.Within logical.length) :
    HeapCalls.membership (relocateValue rename needle) (.ref (rename address)) negated physical =
      (HeapCalls.membership needle (.ref address) negated logical).map
        (fun result => (result.1.map (relocateValue rename), physical)) := by
  have moved := layout.lookup address _ found
  cases needle with
  | scalar scalar => simp [HeapCalls.membership, found, moved, relocateObject, relocateValue, Except.map]
  | ref keyAddress =>
    have queried := layout.membershipKey closed (.ref keyAddress) inside
    simp only [relocateValue] at queried
    change HeapCalls.membership (.ref (rename keyAddress)) (.ref (rename address)) negated physical = _
    cases query : HeapCalls.membershipKey (.ref keyAddress) logical with
    | none => simp [HeapCalls.membership, found, moved, relocateObject, queried, query, eval_bind]
    | some pair =>
      rcases pair with ⟨outcome, after⟩
      have unchanged := membershipKey_keeps_heap logical after closed (.ref keyAddress) inside outcome query
      subst after
      cases outcome <;> simp [HeapCalls.membership, found, moved, relocateObject,
        queried, query, eval_bind, Except.map]
      rfl

theorem RuntimeLayout.membership_keyDict (layout : RuntimeLayout logical physical rename)
    (closed : Closed logical) (address : Nat) (entries : List (HashDict.Entry Value)) (needle : Value)
    (negated : Bool) (found : logical[address]? = some (.keyDict entries))
    (inside : needle.edge.Within logical.length) :
    HeapCalls.membership (relocateValue rename needle) (.ref (rename address)) negated physical =
      (HeapCalls.membership needle (.ref address) negated logical).map
        (fun result => (result.1.map (relocateValue rename), physical)) := by
  have moved := layout.lookup address _ found
  have same := layout.keyOf closed needle inside
  have lookup := hashDict_lookup_relocates entries rename
  cases resolved : Mutable.keyOf logical needle with
  | none =>
    simp [HeapCalls.membership, found, moved, relocateObject, Mutable.hashKey, same, resolved, eval_bind]
  | some outcome =>
    cases outcome <;> simp [HeapCalls.membership, found, moved, relocateObject, Mutable.hashKey,
      same, resolved, eval_bind, lookup, Except.map]
    rfl

theorem RuntimeLayout.membership_dict (layout : RuntimeLayout logical physical rename)
    (closed : Closed logical) (address : Nat) (entries : List (Constant × Value)) (needle : Value)
    (negated : Bool) (found : logical[address]? = some (.dict entries))
    (inside : needle.edge.Within logical.length) :
    HeapCalls.membership (relocateValue rename needle) (.ref (rename address)) negated physical =
      (HeapCalls.membership needle (.ref address) negated logical).map
        (fun result => (result.1.map (relocateValue rename), physical)) := by
  have moved := layout.lookup address _ found
  cases needle with
  | scalar key =>
    have lookup := scalarDict_lookup_relocates entries rename key
    change HeapCalls.membership (.scalar key) (.ref (rename address)) negated physical = _
    simp [HeapCalls.membership, found, moved, relocateObject, lookup, Except.map]
    rfl
  | ref keyAddress =>
    have same := layout.keyOf closed (.ref keyAddress) inside
    simp only [relocateValue] at same
    change HeapCalls.membership (.ref (rename keyAddress)) (.ref (rename address)) negated physical = _
    have promoted := promoteDictionary_relocates entries rename
    simp only [relocateHashEntries] at promoted
    have lookup := hashDict_lookup_relocates (Mutable.promoteDictionary entries) rename
    cases resolved : Mutable.keyOf logical (.ref keyAddress) with
    | none =>
      simp [HeapCalls.membership, found, moved, relocateObject, Mutable.hashKey, same, resolved, eval_bind]
    | some outcome =>
      cases outcome <;> simp [HeapCalls.membership, found, moved, relocateObject, Mutable.hashKey,
        same, resolved, eval_bind, promoted, lookup, Except.map]
      rfl

end FormalSW.PyAst.Mutable.Relocation

namespace FormalSW.PyAst.HeapCalls
set_option Elab.async false

variable {module : Module} {env : Env} {base expression : Expr}
    {heap middle afterItem finalHeap : Heap} {address : Nat} {value answer : Value}
    {globals : Mutable.Globals}

/-- The receiver is captured before the item runs; the actual add then sees the resulting heap. -/
theorem Evaluates.add_result
    (receiver : Evaluates (globals := globals) module env base heap (.ref address) middle)
    (bound : Mutable.addReceiver (.ref address) middle = some (.ok address, middle))
    (item : Evaluates (globals := globals) module env expression middle value afterItem)
    (added : Mutable.addItem address value afterItem = some (.ok answer, finalHeap)) :
    Evaluates (globals := globals) module env (.call (.attribute base "add") [expression]) heap answer finalHeap := by
  intro anchors stack
  apply Reaches.next rfl
  apply (receiver anchors _).trans
  apply Reaches.next (following := ⟨.expr expression env,
    .arguments (.add address) [] [] env :: stack, middle⟩)
    (by
      cases found : middle[address]? with
      | none => simp [Mutable.addReceiver, found, Mutable.unsupported] at bound
      | some object =>
        cases object with
        | set items | keySet items => simp [step, run, found, bound, argumentsState]
        | list items | tuple items | bytearray bytes | dict entries | keyDict entries
        | «instance» origin name fields | dataInstance origin name frozen declared fields =>
          simp [Mutable.addReceiver, found, Mutable.error] at bound)
  apply (item anchors _).trans
  apply Reaches.next (following := ⟨.operation (.add address) [value], stack, afterItem⟩) rfl
  exact .next (by simp [step, result, run, primitive, added]) .refl

end FormalSW.PyAst.HeapCalls
