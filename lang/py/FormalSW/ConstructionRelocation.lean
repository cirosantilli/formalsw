import lang.py.FormalSW.SetRelocation
import lang.py.FormalSW.SetDifferenceCalls

/-! Fresh containers and sequential set construction preserve execution layouts. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

variable {logical physical : Heap} {rename : Nat → Nat}

/-- A fresh cell can point to old objects or itself without changing empty-tuple interning. -/
theorem ExecutionLayout.append_object (layout : ExecutionLayout logical physical rename)
    (object : Object) (nonempty : object ≠ .tuple [])
    (inside : ObjectWithin (logical.length + 1) object) :
    let nextMap := extendMap rename logical.length physical.length
    ExecutionLayout (logical ++ [object]) (physical ++ [relocateObject nextMap object]) nextMap := by
  dsimp only
  refine ⟨layout.runtime.allocate layout.closed object, layout.closed.append_object object inside, ?_⟩
  intro address selected
  rw [emptyTupleAddress_append_nonempty _ _ nonempty] at selected
  rw [emptyTupleAddress_append_nonempty _ _ (by simpa using nonempty)]
  have bound := (List.getElem?_eq_some_iff.mp (emptyTupleAddress_lookup selected)).1
  simpa only [extendMap_old _ _ _ _ bound] using layout.interned address selected

/-- Objects containing only old references can be relocated before the address map grows. -/
theorem ExecutionLayout.append_existing (layout : ExecutionLayout logical physical rename)
    (object : Object) (nonempty : object ≠ .tuple []) (inside : ObjectWithin logical.length object) :
    ExecutionLayout (logical ++ [object]) (physical ++ [relocateObject rename object])
      (extendMap rename logical.length physical.length) := by
  have same := relocateObject_congr (extendMap rename logical.length physical.length) rename
    logical.length object (fun _ bound => extendMap_old _ _ _ _ bound) inside
  simpa only [same] using layout.append_object object nonempty (inside.mono (by omega))

theorem ExecutionLayout.allocateSet (layout : ExecutionLayout logical physical rename) (items : List Constant) :
    Mutable.allocateSet items logical = some (.ok (.ref logical.length), logical ++ [.set items]) ∧
    Mutable.allocateSet items physical = some (.ok (.ref physical.length), physical ++ [.set items]) ∧
    ExecutionLayout (logical ++ [.set items]) (physical ++ [.set items])
      (extendMap rename logical.length physical.length) := by
  exact ⟨rfl, rfl, layout.append_existing (.set items) (by simp) (by simp [ObjectWithin, objectValues])⟩

theorem ExecutionLayout.allocateBuffer (layout : ExecutionLayout logical physical rename) (bytes : List UInt8) :
    Mutable.allocateBuffer bytes logical = some (.ok (.ref logical.length), logical ++ [.bytearray bytes]) ∧
    Mutable.allocateBuffer bytes physical = some (.ok (.ref physical.length), physical ++ [.bytearray bytes]) ∧
    ExecutionLayout (logical ++ [.bytearray bytes]) (physical ++ [.bytearray bytes])
      (extendMap rename logical.length physical.length) := by
  exact ⟨rfl, rfl, layout.append_existing (.bytearray bytes) (by simp) (by simp [ObjectWithin, objectValues])⟩

theorem ExecutionLayout.allocateDict (layout : ExecutionLayout logical physical rename)
    (entries : List (Constant × Value)) (inside : ObjectWithin logical.length (.dict entries)) :
    Mutable.allocateDict entries logical = some (.ok (.ref logical.length), logical ++ [.dict entries]) ∧
    Mutable.allocateDict (entries.map fun entry => (entry.1, relocateValue rename entry.2)) physical =
      some (.ok (.ref physical.length),
        physical ++ [.dict (entries.map fun entry => (entry.1, relocateValue rename entry.2))]) ∧
    ExecutionLayout (logical ++ [.dict entries])
      (physical ++ [.dict (entries.map fun entry => (entry.1, relocateValue rename entry.2))])
      (extendMap rename logical.length physical.length) := by
  exact ⟨rfl, rfl, layout.append_existing (.dict entries) (by simp) inside⟩

/-- A sequence of insertions transports the actual intermediate states and stops at the first error. -/
theorem ExecutionLayout.addItems (items : List Value) (layout : ExecutionLayout logical physical rename)
    (address : Nat) (addressInside : address < logical.length)
    (inside : ∀ value ∈ items, value.edge.Within logical.length)
    (outcome : Except ExceptionObject (List Value)) (after : Heap)
    (executed : items.mapM (Mutable.addItem address) logical = some (outcome, after)) :
    ∃ other,
      (items.map (relocateValue rename)).mapM (Mutable.addItem (rename address)) physical =
        some (outcome.map (List.map (relocateValue rename)), other) ∧
      ExecutionLayout after other rename ∧ after.length = logical.length := by
  induction items generalizing logical physical outcome after with
  | nil =>
    have same : some (.ok [], logical) = some (outcome, after) := executed
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
    exact ⟨physical, rfl, layout, rfl⟩
  | cons item rest ih =>
    cases first : Mutable.addItem address item logical with
    | none => simp [List.mapM_cons, first, eval_bind] at executed
    | some pair =>
      rcases pair with ⟨result, middle⟩
      obtain ⟨otherMiddle, otherFirst, middleLayout, sameLength, _⟩ :=
        layout.addItem address item addressInside (inside item (by simp)) _ _ first
      cases result with
      | error exception =>
        have same : some (.error exception, middle) = some (outcome, after) := by
          simpa [List.mapM_cons, first, eval_bind] using executed
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
        refine ⟨otherMiddle, ?_, middleLayout, sameLength⟩
        simp [List.mapM_cons, otherFirst, eval_bind, Except.map]
      | ok value =>
        cases remaining : rest.mapM (Mutable.addItem address) middle with
        | none => simp [List.mapM_cons, first, remaining, eval_bind] at executed
        | some tail =>
          rcases tail with ⟨tailOutcome, finalHeap⟩
          obtain ⟨other, otherRemaining, finalLayout, finalLength⟩ := ih middleLayout
            (by simpa [sameLength] using addressInside)
            (fun value member => by simpa [sameLength] using inside value (by simp [member]))
            tailOutcome finalHeap remaining
          simp only [List.mapM_map] at otherRemaining
          cases tailOutcome with
          | error exception =>
            have same : some (.error exception, finalHeap) = some (outcome, after) := by
              simpa [List.mapM_cons, first, remaining, eval_bind] using executed
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
            refine ⟨other, ?_, finalLayout, finalLength.trans sameLength⟩
            simp [List.mapM_cons, otherFirst, otherRemaining, eval_bind, Except.map]
          | ok values =>
            have same : some (.ok (value :: values), finalHeap) = some (outcome, after) := by
              simpa [List.mapM_cons, first, remaining, eval_bind, Except.map] using executed
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
            refine ⟨other, ?_, finalLayout, finalLength.trans sameLength⟩
            simp [List.mapM_cons, otherFirst, otherRemaining, eval_bind, Except.map]

/-- Sequential insertion cannot turn an unsupported operation into a supported one. -/
theorem ExecutionLayout.addItems_unsupported (items : List Value)
    (layout : ExecutionLayout logical physical rename) (address : Nat)
    (addressInside : address < logical.length)
    (inside : ∀ value ∈ items, value.edge.Within logical.length) :
    (items.map (relocateValue rename)).mapM (Mutable.addItem (rename address)) physical = none ↔
      items.mapM (Mutable.addItem address) logical = none := by
  induction items generalizing logical physical with
  | nil => simp
  | cons item rest ih =>
    have firstUnsupported := layout.runtime.addItem_unsupported layout.closed address item
      addressInside (inside item (by simp))
    cases first : Mutable.addItem address item logical with
    | none =>
      have otherFirst := firstUnsupported.mpr first
      simp [List.mapM_cons, first, otherFirst, eval_bind]
    | some pair =>
      rcases pair with ⟨result, middle⟩
      obtain ⟨otherMiddle, otherFirst, middleLayout, sameLength, _⟩ :=
        layout.addItem address item addressInside (inside item (by simp)) _ _ first
      cases result with
      | error exception => simp [List.mapM_cons, first, otherFirst, eval_bind, Except.map]
      | ok value =>
        have remaining := ih middleLayout (by simpa [sameLength] using addressInside)
          (fun value member => by simpa [sameLength] using inside value (by simp [member]))
        simp only [List.mapM_map] at remaining
        simp [List.mapM_cons, first, otherFirst, eval_bind, Except.map]
        simpa only [Option.eq_none_iff_forall_ne_some, Prod.forall] using remaining

/-- Proof-facing scalar test with the same recursive definition as the runtime's private test. -/
def scalarValues : List Value → Bool
  | [] => true
  | .scalar _ :: rest => scalarValues rest
  | .ref _ :: _ => false

theorem scalarValues_relocates (items : List Value) (rename : Nat → Nat) :
    scalarValues (items.map (relocateValue rename)) = scalarValues items := by
  induction items with
  | nil => rfl
  | cons item rest ih => cases item <;> simp [scalarValues, relocateValue, ih]

theorem scalarValues_true (items : List Value) (all : scalarValues items = true) :
    ∃ values : List Constant, items = values.map Value.scalar := by
  induction items with
  | nil => exact ⟨[], rfl⟩
  | cons item rest ih =>
    cases item with
    | ref address => simp [scalarValues] at all
    | scalar value =>
      obtain ⟨values, rfl⟩ := ih all
      exact ⟨value :: values, rfl⟩

theorem allocateSetValues_eq (items : List Value) :
    Mutable.allocateSetValues items = (do
      if scalarValues items then
        let keys ← items.mapM Mutable.setKey
        Mutable.allocateSet (keys.foldl ScalarSet.insert [])
      else
        let address := (← get).length
        let _ ← Mutable.allocateSet []
        let _ ← items.mapM (Mutable.addItem address)
        return .ref address : Eval Value) := by
  unfold Mutable.allocateSetValues
  congr 1
  induction items with
  | nil => rfl
  | cons item rest ih =>
    cases item with
    | scalar value => exact ih
    | ref address => rfl

/-- Construction extends the address map once, including when a later insertion raises. -/
theorem ExecutionLayout.allocateSetValues (layout : ExecutionLayout logical physical rename)
    (items : List Value) (inside : ∀ value ∈ items, value.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : Mutable.allocateSetValues items logical = some (outcome, after)) :
    let nextMap := extendMap rename logical.length physical.length
    ∃ other,
      Mutable.allocateSetValues (items.map (relocateValue rename)) physical =
        some (outcome.map (relocateValue nextMap), other) ∧
      ExecutionLayout after other nextMap ∧ after.length = logical.length + 1 ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length) := by
  dsimp only
  by_cases scalars : scalarValues items = true
  · obtain ⟨values, rfl⟩ := scalarValues_true items scalars
    rw [Mutable.allocateSetValues_scalars] at executed
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
    refine ⟨physical ++ [.set (values.foldl ScalarSet.insert [])], ?_,
      (layout.allocateSet _).2.2, by simp, ?_⟩
    · have mapped : (values.map Value.scalar).map (relocateValue rename) = values.map Value.scalar := by
        simp [List.map_map, relocateValue, Function.comp_def]
      simp [mapped, Mutable.allocateSetValues_scalars, Except.map, relocateValue]
    · intro returned equal
      have same : returned = .ref logical.length := by simpa using equal.symm
      simp [same, Value.edge, Graph.Edge.Within]
  · have notScalars : scalarValues items = false := Bool.eq_false_iff.mpr scalars
    let nextMap := extendMap rename logical.length physical.length
    have mapped : items.map (relocateValue nextMap) = items.map (relocateValue rename) := by
      apply List.map_congr_left
      intro value member
      exact relocateValue_congr _ _ logical.length value
        (fun _ bound => extendMap_old _ _ _ _ bound) (inside value member)
    have initial := (layout.allocateSet []).2.2
    cases inserted : items.mapM (Mutable.addItem logical.length) (logical ++ [.set []]) with
    | none =>
      simp [allocateSetValues_eq, notScalars, Mutable.allocateSet, eval_bind, inserted] at executed
    | some pair =>
      rcases pair with ⟨result, middle⟩
      obtain ⟨other, otherInserted, finalLayout, sameLength⟩ := initial.addItems items logical.length
        (by simp) (fun value member => by
          have bound := inside value member
          cases value with
          | scalar scalar => trivial
          | ref address => simpa only [Value.edge, Graph.Edge.Within, List.length_append,
              List.length_singleton] using Nat.lt_succ_of_lt bound) _ _ inserted
      change ExecutionLayout middle other nextMap at finalLayout
      have finalLength : middle.length = logical.length + 1 := by simpa using sameLength
      change (items.map (relocateValue nextMap)).mapM (Mutable.addItem (nextMap logical.length))
        (physical ++ [.set []]) = some (result.map (List.map (relocateValue nextMap)), other) at otherInserted
      simp only [nextMap, extendMap_new, List.mapM_map] at otherInserted
      cases result with
      | error exception =>
        have same : some (.error exception, middle) = some (outcome, after) := by
          simpa [allocateSetValues_eq, notScalars, Mutable.allocateSet, eval_bind, inserted] using executed
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
        refine ⟨other, ?_, finalLayout, finalLength, ?_⟩
        · rw [← mapped]
          simp [allocateSetValues_eq, scalarValues_relocates, notScalars, Mutable.allocateSet,
            eval_bind, otherInserted, nextMap, Except.map]
        · intro returned impossible
          cases impossible
      | ok values =>
        have same : some (.ok (.ref logical.length), middle) = some (outcome, after) := by
          simpa [allocateSetValues_eq, notScalars, Mutable.allocateSet, eval_bind, inserted,
            Except.map] using executed
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
        refine ⟨other, ?_, finalLayout, finalLength, ?_⟩
        · rw [← mapped]
          simp [allocateSetValues_eq, scalarValues_relocates, notScalars, Mutable.allocateSet,
            eval_bind, otherInserted, nextMap, Except.map, relocateValue]
        · intro returned equal
          have same : returned = .ref logical.length := by simpa using equal.symm
          simp [same, Value.edge, Graph.Edge.Within, finalLength]

/-- An unsupported insertion stays unsupported even when the other heap contains private cells. -/
theorem ExecutionLayout.allocateSetValues_unsupported (layout : ExecutionLayout logical physical rename)
    (items : List Value) (inside : ∀ value ∈ items, value.edge.Within logical.length) :
    Mutable.allocateSetValues (items.map (relocateValue rename)) physical = none ↔
      Mutable.allocateSetValues items logical = none := by
  by_cases scalars : scalarValues items = true
  · obtain ⟨values, rfl⟩ := scalarValues_true items scalars
    have mapped : (values.map Value.scalar).map (relocateValue rename) = values.map Value.scalar := by
      simp [List.map_map, relocateValue, Function.comp_def]
    simp [mapped, Mutable.allocateSetValues_scalars]
  · have notScalars : scalarValues items = false := Bool.eq_false_iff.mpr scalars
    let nextMap := extendMap rename logical.length physical.length
    have mapped : items.map (relocateValue nextMap) = items.map (relocateValue rename) := by
      apply List.map_congr_left
      intro value member
      exact relocateValue_congr _ _ logical.length value
        (fun _ bound => extendMap_old _ _ _ _ bound) (inside value member)
    have initial := (layout.allocateSet []).2.2
    have inserted := initial.addItems_unsupported items logical.length (by simp)
      (fun value member => by
        have bound := inside value member
        cases value with
        | scalar scalar => trivial
        | ref address => simpa only [Value.edge, Graph.Edge.Within, List.length_append,
            List.length_singleton] using Nat.lt_succ_of_lt bound)
    change (items.map (relocateValue nextMap)).mapM (Mutable.addItem (nextMap logical.length))
      (physical ++ [.set []]) = none ↔
        items.mapM (Mutable.addItem logical.length) (logical ++ [.set []]) = none at inserted
    simp only [nextMap, extendMap_new, List.mapM_map] at inserted
    rw [← mapped]
    simp [allocateSetValues_eq, scalarValues_relocates, notScalars, Mutable.allocateSet,
      eval_bind, nextMap]
    simpa only [Option.eq_none_iff_forall_ne_some, Prod.forall] using inserted

end FormalSW.PyAst.Mutable.Relocation
