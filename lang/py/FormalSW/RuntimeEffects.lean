import lang.py.FormalSW.TupleRelocation

/-! Closed runtime layouts compose field mutation with subsequent allocations. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

theorem ObjectWithin.mono {before after : Nat} {object : Object}
    (inside : ObjectWithin before object) (larger : before ≤ after) : ObjectWithin after object := by
  intro value member
  have bound := inside value member
  cases value with
  | scalar value => trivial
  | ref address => exact Nat.lt_of_lt_of_le bound larger

theorem Closed.set {heap : Heap} (closed : Closed heap) (address : Nat) (object : Object)
    (inside : ObjectWithin heap.length object) : Closed (heap.set address object) := by
  intro current member
  have bounded : ObjectWithin heap.length current := by
    rcases List.mem_or_eq_of_mem_set member with original | same
    · exact closed current original
    · simpa only [same] using inside
  simpa only [List.length_set] using bounded

theorem Closed.append_object {heap : Heap} (closed : Closed heap) (object : Object)
    (inside : ObjectWithin (heap.length + 1) object) : Closed (heap ++ [object]) := by
  intro current member
  rcases List.mem_append.mp member with original | fresh
  · exact (closed current original).mono (by simp)
  · simpa only [List.mem_singleton.mp fresh, List.length_append, List.length_singleton] using inside

theorem putField_within (fields : List (String × Value)) (name : String) (value : Value)
    (limit : Nat) (old : ∀ field ∈ fields, field.2.edge.Within limit)
    (inside : value.edge.Within limit) :
    ∀ field ∈ putField fields name value, field.2.edge.Within limit := by
  induction fields with
  | nil => simpa [putField] using inside
  | cons field fields ih =>
    rcases field with ⟨key, previous⟩
    have first := old (key, previous) (by simp)
    have rest : ∀ field ∈ fields, field.2.edge.Within limit := by
      intro field member
      exact old field (by simp [member])
    by_cases same : key = name
    · simpa [putField, same] using And.intro inside rest
    · simpa [putField, same] using And.intro first (ih rest)

/-- Every supported field write either updates one instance or raises without changing memory. -/
inductive FieldWriteEffect (heap : Heap) (name : String) (value : Value) :
    Except ExceptionObject Value → Heap → Prop where
  | error (exception : ExceptionObject) : FieldWriteEffect heap name value (.error exception) heap
  | plain (address : Nat) (origin className : String) (fields : List (String × Value))
      (found : heap[address]? = some (.instance origin className fields)) :
      FieldWriteEffect heap name value (.ok (.scalar .none))
        (heap.set address (.instance origin className (putField fields name value)))
  | dataInstance (address : Nat) (origin className : String) (declared : List String)
      (fields : List (String × Value))
      (found : heap[address]? = some (.dataInstance origin className false declared fields)) :
      FieldWriteEffect heap name value (.ok (.scalar .none))
        (heap.set address (.dataInstance origin className false declared (putField fields name value)))

theorem writeField_effect (heap after : Heap) (receiver : Value) (name : String) (value : Value)
    (outcome : Except ExceptionObject Value)
    (executed : Mutable.writeField receiver name value heap = some (outcome, after)) :
    FieldWriteEffect heap name value outcome after := by
  have failed (exception : ExceptionObject)
      (run : Mutable.writeField receiver name value heap = some (.error exception, heap)) :
      FieldWriteEffect heap name value outcome after := by
    rw [run] at executed
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
    exact .error exception
  by_cases special : name = "__class__" ∨ name = "__dict__" ∨ name = "__weakref__"
  · simp [Mutable.writeField, special, unsupported] at executed
  · cases receiver with
    | scalar scalar =>
      apply failed ⟨"AttributeError", []⟩
      simp [Mutable.writeField, instanceData, special, error]
    | ref address =>
      cases found : heap[address]? with
      | none => simp [Mutable.writeField, instanceData, found, special, unsupported] at executed
      | some object =>
        cases object with
        | «instance» origin className fields =>
          have run : Mutable.writeField (.ref address) name value heap =
              some (.ok (.scalar .none),
                heap.set address (.instance origin className (putField fields name value))) := by
            simp [Mutable.writeField, instanceData, special, found, Except.map]
          rw [run] at executed
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
          exact .plain address origin className fields found
        | dataInstance origin className frozen declared fields =>
          cases frozen with
          | true =>
            apply failed ⟨"FrozenInstanceError", []⟩
            simp [Mutable.writeField, instanceData, special, found, error]
          | false =>
            have run : Mutable.writeField (.ref address) name value heap =
                some (.ok (.scalar .none), heap.set address
                  (.dataInstance origin className false declared (putField fields name value))) := by
              simp [Mutable.writeField, instanceData, special, found, Except.map]
            rw [run] at executed
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
            exact .dataInstance address origin className declared fields found
        | list items | tuple items | bytearray bytes | set items | keySet items
        | dict entries | keyDict entries =>
          apply failed ⟨"AttributeError", []⟩
          simp [Mutable.writeField, instanceData, special, found, error]

variable {heap after : Heap} {name : String} {value : Value} {outcome : Except ExceptionObject Value}

theorem FieldWriteEffect.length (effect : FieldWriteEffect heap name value outcome after) :
    after.length = heap.length := by
  cases effect <;> simp

theorem FieldWriteEffect.emptyTuple (effect : FieldWriteEffect heap name value outcome after) :
    emptyTupleAddress after = emptyTupleAddress heap := by
  cases effect with
  | error => rfl
  | plain address origin className fields found =>
    exact emptyTupleAddress_set _ _ _ _ found (by simp) (by simp)
  | dataInstance address origin className declared fields found =>
    exact emptyTupleAddress_set _ _ _ _ found (by simp) (by simp)

theorem FieldWriteEffect.closed (effect : FieldWriteEffect heap name value outcome after)
    (closed : Closed heap) (inside : value.edge.Within heap.length) : Closed after := by
  cases effect with
  | error => exact closed
  | plain address origin className fields found
  | dataInstance address origin className declared fields found =>
    have old := closed _ (List.mem_of_getElem? found)
    have bounded : ∀ field ∈ fields, field.2.edge.Within heap.length := by
      intro field member
      exact old field.2 (List.mem_map.mpr ⟨field, member, rfl⟩)
    apply closed.set
    intro stored member
    obtain ⟨field, present, rfl⟩ := List.mem_map.mp member
    exact putField_within fields name value heap.length bounded inside field present

theorem FieldWriteEffect.result (effect : FieldWriteEffect heap name value outcome after)
    (returned : Value) (success : outcome = .ok returned) : returned = .scalar .none := by
  cases effect <;> simp_all

/-- The invariants required to run further operations on relocated caller objects. -/
structure ExecutionLayout (logical physical : Heap) (rename : Nat → Nat) : Prop where
  runtime : RuntimeLayout logical physical rename
  closed : Closed logical
  interned : EmptyTuplesAligned logical physical rename

theorem ExecutionLayout.refl (heap : Heap) (closed : Closed heap) : ExecutionLayout heap heap id :=
  ⟨RuntimeLayout.refl heap, closed, EmptyTuplesAligned.refl heap⟩

variable {logical physical : Heap} {rename : Nat → Nat}

/-- Solver-private writes retain the caller's execution invariants when interning is unchanged. -/
theorem ExecutionLayout.preserves {after : Heap}
    (layout : ExecutionLayout logical physical rename)
    (related : RuntimeLayout logical after rename)
    (same : emptyTupleAddress after = emptyTupleAddress physical) :
    ExecutionLayout logical after rename :=
  ⟨related, layout.closed, layout.interned.preserves same⟩

theorem RuntimeLayout.truth (layout : RuntimeLayout logical physical rename) (value : Value)
    (inside : value.edge.Within logical.length) :
    Mutable.truth (relocateValue rename value) physical =
      (Mutable.truth value logical).map (fun result => (result.1, physical)) := by
  cases value with
  | scalar scalar => simp [Mutable.truth, relocateValue]
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    cases object : logical[address] <;>
      simp only [object, relocateObject] at moved <;>
      simp [Mutable.truth, relocateValue, found, object, moved]

theorem RuntimeLayout.length (layout : RuntimeLayout logical physical rename) (value : Value)
    (inside : value.edge.Within logical.length) :
    Mutable.length (relocateValue rename value) physical =
      (Mutable.length value logical).map
        (fun result => (result.1.map (relocateValue rename), physical)) := by
  cases value with
  | scalar scalar => cases scalar <;> simp [Mutable.length, relocateValue, error, Except.map]
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    cases object : logical[address] <;>
      simp only [object, relocateObject] at moved <;>
      simp [Mutable.length, relocateValue, found, object, moved, error, Except.map]

theorem RuntimeLayout.sequence (layout : RuntimeLayout logical physical rename) (value : Value)
    (inside : value.edge.Within logical.length) :
    Mutable.sequence (relocateValue rename value) physical =
      (Mutable.sequence value logical).map
        (fun result => (result.1.map (List.map (relocateValue rename)), physical)) := by
  cases value with
  | scalar scalar =>
    cases scalar <;> simp [Mutable.sequence, relocateValue, error, Except.map,
      List.map_map, Function.comp_def]
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    cases object : logical[address] <;>
      simp only [object, relocateObject] at moved <;>
      simp [Mutable.sequence, relocateValue, found, object, moved, error, unsupported,
        Except.map, List.map_map, Function.comp_def]

/-- A successful field read returns an existing bounded value and leaves the heap unchanged. -/
theorem readField_bounded (heap after : Heap) (closed : Closed heap) (receiver : Value)
    (name : String) (value : Value)
    (executed : Mutable.readField receiver name heap = some (.ok value, after)) :
    after = heap ∧ value.edge.Within heap.length := by
  by_cases special : name = "__class__" ∨ name = "__dict__" ∨ name = "__weakref__"
  · simp [Mutable.readField, special, unsupported] at executed
  · cases receiver with
    | scalar scalar => simp [Mutable.readField, instanceData, special, error] at executed
    | ref address =>
      cases found : heap[address]? with
      | none => simp [Mutable.readField, instanceData, special, found, unsupported] at executed
      | some object =>
        cases object with
        | «instance» origin className fields | dataInstance origin className frozen declared fields =>
          have old := closed _ (List.mem_of_getElem? found)
          cases field : fields.lookup name with
          | none => simp [Mutable.readField, instanceData, special, found, field, error] at executed
          | some stored =>
            have same : stored = value ∧ heap = after := by
              simpa [Mutable.readField, instanceData, special, found, field] using executed
            obtain ⟨sameValue, sameHeap⟩ := same
            subst value
            subst after
            refine ⟨rfl, old stored ?_⟩
            obtain ⟨beforeFields, afterFields, fieldsEqual, _⟩ := List.lookup_eq_some_iff.mp field
            apply List.mem_map.mpr
            exact ⟨(name, stored), by simp [fieldsEqual], rfl⟩
        | list items | tuple items | bytearray bytes | set items | keySet items
        | dict entries | keyDict entries =>
          simp [Mutable.readField, instanceData, special, found, error] at executed

/-- Successful and exceptional field reads preserve the execution layout. -/
theorem ExecutionLayout.readField (layout : ExecutionLayout logical physical rename)
    (receiver : Value) (name : String) (inside : receiver.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : Mutable.readField receiver name logical = some (outcome, after)) :
    Mutable.readField (relocateValue rename receiver) name physical =
      some (outcome.map (relocateValue rename), physical) ∧
      ExecutionLayout after physical rename ∧ after = logical ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length) := by
  have stationary := (RuntimeLayout.refl logical).readField receiver name inside
  simp only [relocateValue_id, executed, Option.map_some] at stationary
  have same : after = logical := congrArg Prod.snd (Option.some.inj stationary)
  subst after
  refine ⟨?_, layout, rfl, ?_⟩
  · simpa only [executed, Option.map_some] using layout.runtime.readField receiver name inside
  · intro returned success
    exact (readField_bounded logical logical layout.closed receiver name returned
      (by simpa only [success] using executed)).2

/-- Unsupported attribute names remain unsupported in both layouts. -/
theorem RuntimeLayout.writeField_unsupported (layout : RuntimeLayout logical physical rename)
    (receiver : Value) (name : String) (value : Value)
    (inside : receiver.edge.Within logical.length) :
    Mutable.writeField (relocateValue rename receiver) name (relocateValue rename value)
      physical = none ↔ Mutable.writeField receiver name value logical = none := by
  by_cases special : name = "__class__" ∨ name = "__dict__" ∨ name = "__weakref__"
  · simp [Mutable.writeField, special, unsupported]
  · cases receiver with
    | scalar scalar => simp [Mutable.writeField, instanceData, relocateValue, special, error]
    | ref address =>
      have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
      have moved := layout.lookup address _ found
      cases object : logical[address] with
      | dataInstance origin className frozen declared fields =>
        simp only [object, relocateObject] at moved
        cases frozen <;>
          simp [Mutable.writeField, instanceData, relocateValue, special, found, object,
            moved, error, Except.map]
      | list items | tuple items | bytearray bytes | set items | keySet items
      | dict entries | keyDict entries | «instance» origin className fields =>
        simp only [object, relocateObject] at moved
        simp [Mutable.writeField, instanceData, relocateValue, special, found, object,
          moved, error, Except.map]

/-- Actual field updates preserve every invariant needed by subsequent allocations. -/
theorem ExecutionLayout.writeField (layout : ExecutionLayout logical physical rename)
    (receiver : Value) (name : String) (value : Value)
    (receiverInside : receiver.edge.Within logical.length)
    (valueInside : value.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : Mutable.writeField receiver name value logical = some (outcome, after)) :
    ∃ other, Mutable.writeField (relocateValue rename receiver) name (relocateValue rename value)
      physical = some (outcome.map (relocateValue rename), other) ∧
      ExecutionLayout after other rename ∧ after.length = logical.length ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length) := by
  obtain ⟨other, paired, related⟩ :=
    layout.runtime.writeField receiver name value receiverInside outcome after executed
  have effect := writeField_effect logical after receiver name value outcome executed
  have physicalEffect := writeField_effect physical other (relocateValue rename receiver) name
    (relocateValue rename value) _ paired
  refine ⟨other, paired, ⟨related, effect.closed layout.closed valueInside, ?_⟩,
    effect.length, ?_⟩
  · intro address found
    rw [effect.emptyTuple] at found
    rw [physicalEffect.emptyTuple]
    exact layout.interned address found
  · intro returned success
    rw [effect.result returned success]
    trivial

theorem ExecutionLayout.allocate_list (layout : ExecutionLayout logical physical rename)
    (items : List Value) (inside : ∀ value ∈ items, value.edge.Within logical.length) :
    let nextMap := extendMap rename logical.length physical.length
    Mutable.allocate items logical = some (.ok (.ref logical.length), logical ++ [.list items]) ∧
    Mutable.allocate (items.map (relocateValue rename)) physical =
      some (.ok (.ref physical.length), physical ++ [.list (items.map (relocateValue rename))]) ∧
    ExecutionLayout (logical ++ [.list items])
      (physical ++ [.list (items.map (relocateValue rename))]) nextMap := by
  obtain ⟨left, right, related⟩ := layout.runtime.allocate_list layout.closed items inside
  refine ⟨left, right, related, layout.closed.append_object _ ?_, ?_⟩
  · exact (show ObjectWithin logical.length (.list items) from inside).mono (by omega)
  · intro address selected
    rw [emptyTupleAddress_append_nonempty _ _ (by simp)] at selected
    rw [emptyTupleAddress_append_nonempty _ _ (by simp)]
    have inside := (List.getElem?_eq_some_iff.mp (emptyTupleAddress_lookup selected)).1
    simpa only [extendMap_old _ _ _ _ inside] using layout.interned address selected

theorem ExecutionLayout.allocateTuple (layout : ExecutionLayout logical physical rename)
    (items : List Value) (inside : ∀ value ∈ items, value.edge.Within logical.length) :
    ∃ left right leftAfter rightAfter nextMap,
      Mutable.allocateTuple items logical = some (.ok (.ref left), leftAfter) ∧
      Mutable.allocateTuple (items.map (relocateValue rename)) physical =
        some (.ok (.ref right), rightAfter) ∧
      ExecutionLayout leftAfter rightAfter nextMap ∧
      left < leftAfter.length ∧ nextMap left = right ∧
      (∀ index < logical.length, nextMap index = rename index) := by
  obtain ⟨left, right, leftAfter, rightAfter, nextMap, leftRun, rightRun,
      related, interned, closed, inside, same, old⟩ :=
    layout.runtime.allocateTuple layout.closed layout.interned items inside
  exact ⟨left, right, leftAfter, rightAfter, nextMap, leftRun, rightRun,
    ⟨related, closed, interned⟩, inside, same, old⟩

end FormalSW.PyAst.Mutable.Relocation
