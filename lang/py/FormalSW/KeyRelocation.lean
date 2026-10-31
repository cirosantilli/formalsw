import lang.py.FormalSW.RuntimeEffects

/-! Immutable key resolution is independent of private allocations and reference placement. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

/-- A proof-facing form of the runtime's private, left-to-right key collector. -/
def collectResolved (resolve : Value → Option (Except ExceptionObject HashKey)) :
    List Value → Option (Except ExceptionObject (List HashKey))
  | [] => some (.ok [])
  | value :: rest => do
      match ← resolve value with
      | .error exception => return .error exception
      | .ok key => return (← collectResolved resolve rest).map (key :: ·)

/-- This equation refers to the actual runtime resolver, including unsupported objects. -/
theorem keyOfFuel_ref (heap : Heap) (fuel address : Nat) :
    keyOfFuel heap (fuel + 1) (.ref address) = match heap[address]? with
      | some (.tuple items) =>
          (collectResolved (keyOfFuel heap fuel) items).map (Except.map HashKey.tuple)
      | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) | none => none
      | some _ => some (.error { typeName := "TypeError", args := [] }) := by
  unfold keyOfFuel
  cases found : heap[address]? with
  | none => rfl
  | some object =>
    cases object with
    | tuple items =>
      dsimp only
      congr 1
      clear found
      induction items with
      | nil => rfl
      | cons value rest ih =>
        rw [collectResolved, ← ih]
        rfl
    | list items | bytearray bytes | set items | keySet items | dict entries | keyDict entries
    | «instance» origin name fields | dataInstance origin name frozen declared fields => rfl

/-- Once a finite resolution is known, more recursion allowance preserves that exact result. -/
def ResolutionExtends {α : Type} (left right : Option α) : Prop :=
  ∀ result, left = some result → right = some result

theorem ResolutionExtends.map {α β : Type} {left right : Option α}
    (extension : ResolutionExtends left right) (f : α → β) :
    ResolutionExtends (left.map f) (right.map f) := by
  intro result found
  cases first : left with
  | none => simp [first] at found
  | some value =>
    have same := extension value first
    simpa [first, same] using found

theorem collectResolved_extends (left right : Value → Option (Except ExceptionObject HashKey))
    (items : List Value) (extension : ∀ value ∈ items, ResolutionExtends (left value) (right value)) :
    ResolutionExtends (collectResolved left items) (collectResolved right items) := by
  induction items with
  | nil => intro result found; exact found
  | cons value rest ih =>
    intro result found
    cases first : left value with
    | none => simp [collectResolved, first] at found
    | some outcome =>
      have same := extension value (by simp) outcome first
      cases outcome with
      | error exception => simpa [collectResolved, first, same] using found
      | ok key =>
        have tail := ih (fun item member => extension item (by simp [member]))
        cases remaining : collectResolved left rest with
        | none => simp [collectResolved, first, remaining] at found
        | some keys =>
          have retained := tail keys remaining
          simpa [collectResolved, first, same, remaining, retained] using found

theorem keyOfFuel_step_extends (heap : Heap) (fuel : Nat) (value : Value) :
    ResolutionExtends (keyOfFuel heap fuel value) (keyOfFuel heap (fuel + 1) value) := by
  induction fuel generalizing value with
  | zero =>
    cases value with
    | scalar value => intro result found; exact found
    | ref address => intro result found; simp [keyOfFuel] at found
  | succ fuel ih =>
    cases value with
    | scalar value => intro result found; exact found
    | ref address =>
      rw [keyOfFuel_ref, keyOfFuel_ref]
      cases found : heap[address]? with
      | none => intro result impossible; cases impossible
      | some object =>
        cases object with
        | tuple items => exact (collectResolved_extends _ _ items (fun value _ => ih value)).map _
        | list items | bytearray bytes | set items | keySet items | dict entries | keyDict entries
        | «instance» origin name fields | dataInstance origin name frozen declared fields =>
          intro result same
          exact same

/-- An unresolved coordinate becoming resolved strictly increases the finite resolved count. -/
theorem resolved_count_strict {α : Type} (domain : List Nat) (left right : Nat → Option α)
    (extension : ∀ index ∈ domain, ResolutionExtends (left index) (right index))
    (index : Nat) (member : index ∈ domain) (different : right index ≠ left index) :
    domain.countP (fun index => (left index).isSome) <
      domain.countP (fun index => (right index).isSome) := by
  have monotone : ∀ index ∈ domain, (left index).isSome = true → (right index).isSome = true := by
    intro position present defined
    cases found : left position with
    | none => simp [found] at defined
    | some value => simp [extension position present value found]
  have first : left index = none := by
    cases found : left index with
    | none => rfl
    | some value => exact False.elim (different (by rw [extension index member value found, found]))
  have second : (right index).isSome = true := by
    cases found : right index with
    | none => exact False.elim (different (by rw [first, found]))
    | some value => rfl
  obtain ⟨before, after, equal⟩ := List.mem_iff_append.mp member
  subst domain
  have beforeCount := List.countP_mono_left (l := before)
    (fun position present => monotone position (by simp [present]))
  have afterCount := List.countP_mono_left (l := after)
    (fun position present => monotone position (by simp [present]))
  simp only [List.countP_append, List.countP_cons, first, Option.isSome_none, Bool.false_eq_true,
    ↓reduceIte, second] at *
  omega

/-- A monotone partial result at each of finitely many addresses reaches a fixed point.
The step rule rules out a delayed change after a stationary iteration. -/
theorem finite_resolution_stable {α : Type} (limit : Nat) (resolve : Nat → Nat → Option α)
    (extension : ∀ fuel index, index < limit →
      ResolutionExtends (resolve fuel index) (resolve (fuel + 1) index))
    (step : ∀ fuel, (∀ index < limit, resolve (fuel + 1) index = resolve fuel index) →
      ∀ index < limit, resolve (fuel + 2) index = resolve (fuel + 1) index) :
    ∀ index < limit, resolve (limit + 1) index = resolve limit index := by
  classical
  let stable := fun fuel => ∀ index < limit, resolve (fuel + 1) index = resolve fuel index
  have propagate : ∀ fuel extra, stable fuel → stable (fuel + extra) := by
    intro fuel extra same
    induction extra with
    | zero => exact same
    | succ extra ih => simpa [stable, Nat.add_assoc] using step (fuel + extra) ih
  apply Classical.byContradiction
  intro unresolved
  have notStable : ∀ fuel, fuel ≤ limit → ¬stable fuel := by
    intro fuel bound same
    have final := propagate fuel (limit - fuel) same
    have equal : fuel + (limit - fuel) = limit := by omega
    rw [equal] at final
    exact unresolved final
  let count := fun fuel => (List.range limit).countP (fun index => (resolve fuel index).isSome)
  have grows : ∀ fuel, fuel ≤ limit → count fuel < count (fuel + 1) := by
    intro fuel bound
    have differs : ∃ index, index < limit ∧ resolve (fuel + 1) index ≠ resolve fuel index := by
      apply Classical.byContradiction
      intro noDifference
      apply notStable fuel bound
      intro index inside
      apply Classical.byContradiction
      intro different
      exact noDifference ⟨index, inside, different⟩
    obtain ⟨index, inside, different⟩ := differs
    exact resolved_count_strict (List.range limit) (resolve fuel) (resolve (fuel + 1))
      (fun index present => extension fuel index (List.mem_range.mp present))
      index (List.mem_range.mpr inside) different
  have lower : ∀ fuel, fuel ≤ limit + 1 → fuel ≤ count fuel := by
    intro fuel bound
    induction fuel with
    | zero => omega
    | succ fuel ih =>
      have previous := ih (by omega)
      have increased := grows fuel (by omega)
      omega
  have upper : count (limit + 1) ≤ limit := by
    simpa [count] using (List.countP_le_length
      (p := fun index => (resolve (limit + 1) index).isSome) (l := List.range limit))
  have impossible := lower (limit + 1) (by omega)
  omega

theorem keyOfFuel_missing (heap : Heap) (fuel address : Nat) (missing : heap[address]? = none) :
    keyOfFuel heap fuel (.ref address) = none := by
  cases fuel <;> simp [keyOfFuel, missing]

/-- The next iteration only depends on the preceding results at actual heap addresses. -/
theorem keyOfFuel_step_congr (heap : Heap) (left right : Nat)
    (same : ∀ index < heap.length, keyOfFuel heap left (.ref index) = keyOfFuel heap right (.ref index))
    (value : Value) : keyOfFuel heap (left + 1) value = keyOfFuel heap (right + 1) value := by
  have allValues : keyOfFuel heap left = keyOfFuel heap right := by
    funext item
    cases item with
    | scalar scalar => simp [keyOfFuel]
    | ref address =>
      by_cases inside : address < heap.length
      · exact same address inside
      · have missing : heap[address]? = none := List.getElem?_eq_none (by omega)
        rw [keyOfFuel_missing heap left address missing, keyOfFuel_missing heap right address missing]
  cases value with
  | scalar scalar => simp [keyOfFuel]
  | ref address => simp only [keyOfFuel_ref, allValues]

/-- Every result has stabilized after at most one new resolution per heap object. -/
theorem keyOfFuel_stabilized (heap : Heap) (extra : Nat) (value : Value) :
    keyOfFuel heap (heap.length + extra) value = keyOfFuel heap heap.length value := by
  have adjacent := finite_resolution_stable heap.length
    (fun fuel address => keyOfFuel heap fuel (.ref address))
    (fun fuel address _ => keyOfFuel_step_extends heap fuel (.ref address))
    (fun fuel same address _ => keyOfFuel_step_congr heap (fuel + 1) fuel same (.ref address))
  have base : ∀ item, keyOfFuel heap (heap.length + 1) item = keyOfFuel heap heap.length item := by
    intro item
    cases item with
    | scalar scalar => simp [keyOfFuel]
    | ref address =>
      by_cases inside : address < heap.length
      · exact adjacent address inside
      · have missing : heap[address]? = none := List.getElem?_eq_none (by omega)
        rw [keyOfFuel_missing heap _ address missing, keyOfFuel_missing heap _ address missing]
  induction extra generalizing value with
  | zero => rfl
  | succ extra ih =>
    calc
      keyOfFuel heap (heap.length + (extra + 1)) value =
          keyOfFuel heap (heap.length + 1) value :=
        keyOfFuel_step_congr heap (heap.length + extra) heap.length (fun index _ => ih (.ref index)) value
      _ = keyOfFuel heap heap.length value := base value

theorem keyOfFuel_eq_keyOf (heap : Heap) (fuel : Nat) (value : Value)
    (enough : heap.length ≤ fuel) : keyOfFuel heap fuel value = keyOf heap value := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le enough
  exact (keyOfFuel_stabilized heap extra value).trans (keyOfFuel_stabilized heap 1 value).symm

theorem collectResolved_relocates (left right : Value → Option (Except ExceptionObject HashKey))
    (rename : Nat → Nat) (items : List Value)
    (same : ∀ value ∈ items, right (relocateValue rename value) = left value) :
    collectResolved right (items.map (relocateValue rename)) = collectResolved left items := by
  induction items with
  | nil => rfl
  | cons value rest ih =>
    have first := same value (by simp)
    have remaining := ih (fun item member => same item (by simp [member]))
    simp only [List.map_cons, collectResolved, first, remaining]

/-- At a common allowance, resolution follows exactly the relocated tuple graph. -/
theorem RuntimeLayout.keyOfFuel {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (fuel : Nat) (value : Value) (inside : value.edge.Within logical.length) :
    Mutable.keyOfFuel physical fuel (relocateValue rename value) = Mutable.keyOfFuel logical fuel value := by
  induction fuel generalizing value with
  | zero => cases value <;> rfl
  | succ fuel ih =>
    cases value with
    | scalar scalar => rfl
    | ref address =>
      have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
      generalize objectValue : logical[address] = object at found
      have moved := layout.lookup address object found
      have bounded := closed object (List.mem_of_getElem? found)
      cases object with
      | tuple items =>
        simp only [relocateValue, keyOfFuel_ref, found, moved, relocateObject]
        congr 1
        exact collectResolved_relocates _ _ rename items (fun item member => ih item (bounded item member))
      | list items | bytearray bytes | set items | keySet items | dict entries | keyDict entries
      | «instance» origin name fields | dataInstance origin name frozen declared fields =>
        simp [relocateValue, keyOfFuel_ref, found, moved, relocateObject]

/-- Actual key resolution is unchanged even though each heap chooses a different allowance. -/
theorem RuntimeLayout.keyOf {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (value : Value) (inside : value.edge.Within logical.length) :
    Mutable.keyOf physical (relocateValue rename value) = Mutable.keyOf logical value := by
  let fuel := max logical.length physical.length
  calc
    Mutable.keyOf physical (relocateValue rename value) =
        Mutable.keyOfFuel physical fuel (relocateValue rename value) :=
      (keyOfFuel_eq_keyOf physical fuel _ (Nat.le_max_right _ _)).symm
    _ = Mutable.keyOfFuel logical fuel value := layout.keyOfFuel closed fuel value inside
    _ = Mutable.keyOf logical value := keyOfFuel_eq_keyOf logical fuel value (Nat.le_max_left _ _)

theorem ExecutionLayout.hashKey {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (value : Value)
    (inside : value.edge.Within logical.length) :
    Mutable.hashKey (relocateValue rename value) physical =
      (Mutable.hashKey value logical).map (fun result => (result.1, physical)) := by
  simp [Mutable.hashKey, layout.runtime.keyOf layout.closed value inside,
    Option.map_map, Function.comp_def]

/-- Cached keys stay unchanged; only their representatives and associated values move. -/
theorem hashDict_lookup_relocates (entries : List (HashDict.Entry Value))
    (rename : Nat → Nat) (key : HashKey) :
    HashDict.lookup (entries.map fun entry =>
      (entry.1, relocateValue rename entry.2.1, relocateValue rename entry.2.2)) key =
      (HashDict.lookup entries key).map (relocateValue rename) := by
  simp [HashDict.lookup, HashDict.find?, List.find?_map, Option.map_map, Function.comp_def]

/-- Lookup in a tuple-key dictionary transports the actual result, error, or unsupported outcome. -/
theorem RuntimeLayout.getItem_keyDict {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (address : Nat) (entries : List (HashDict.Entry Value)) (subscript : Value)
    (found : logical[address]? = some (.keyDict entries))
    (inside : subscript.edge.Within logical.length) :
    Mutable.getItem (.ref (rename address)) (relocateValue rename subscript) physical =
      (Mutable.getItem (.ref address) subscript logical).map
        (fun result => (result.1.map (relocateValue rename), physical)) := by
  have moved := layout.lookup address _ found
  have same := layout.keyOf closed subscript inside
  cases resolved : Mutable.keyOf logical subscript with
  | none =>
    simp [Mutable.getItem, found, moved, relocateObject, Mutable.hashKey, same, resolved, eval_bind]
  | some outcome =>
    cases outcome with
    | error exception =>
      simp [Mutable.getItem, found, moved, relocateObject, Mutable.hashKey, same, resolved,
        eval_bind, Except.map]
    | ok key =>
      have lookup := hashDict_lookup_relocates entries rename key
      cases selected : HashDict.lookup entries key with
      | some value =>
        simp [Mutable.getItem, found, moved, relocateObject, Mutable.hashKey, same, resolved,
          eval_bind, lookup, selected, Except.map]
      | none =>
        simp [Mutable.getItem, found, moved, relocateObject, Mutable.hashKey, same, resolved,
          eval_bind, lookup, selected]
        cases subscript <;> rfl

/-- A successful dictionary lookup returns one of its stored values. -/
theorem getItem_keyDict_bounded (heap after : Heap) (closed : Closed heap)
    (address : Nat) (entries : List (HashDict.Entry Value)) (subscript value : Value)
    (found : heap[address]? = some (.keyDict entries))
    (executed : Mutable.getItem (.ref address) subscript heap = some (.ok value, after)) :
    value.edge.Within heap.length := by
  have old := closed _ (List.mem_of_getElem? found)
  cases resolved : Mutable.keyOf heap subscript with
  | none => simp [Mutable.getItem, found, Mutable.hashKey, resolved, eval_bind] at executed
  | some outcome =>
    cases outcome with
    | error exception =>
      simp [Mutable.getItem, found, Mutable.hashKey, resolved, eval_bind] at executed
    | ok key =>
      cases selected : HashDict.find? entries key with
      | none =>
        simp [Mutable.getItem, found, Mutable.hashKey, resolved, eval_bind,
          HashDict.lookup, selected] at executed
        cases subscript <;> cases executed
      | some entry =>
        have result : entry.2.2 = value ∧ heap = after := by
          simpa [Mutable.getItem, found, Mutable.hashKey, resolved, eval_bind,
            HashDict.lookup, selected] using executed
        rw [← result.1]
        have member : entry ∈ entries := List.mem_of_find?_eq_some selected
        exact old entry.2.2 (List.mem_flatMap.mpr ⟨entry, member, by simp⟩)

theorem ExecutionLayout.getItem_keyDict {logical physical : Heap} {rename : Nat → Nat}
    (layout : ExecutionLayout logical physical rename) (address : Nat)
    (entries : List (HashDict.Entry Value)) (subscript : Value)
    (found : logical[address]? = some (.keyDict entries))
    (inside : subscript.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : Mutable.getItem (.ref address) subscript logical = some (outcome, after)) :
    Mutable.getItem (.ref (rename address)) (relocateValue rename subscript) physical =
        some (outcome.map (relocateValue rename), physical) ∧
      ExecutionLayout after physical rename ∧ after = logical ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length) := by
  have stationary := (RuntimeLayout.refl logical).getItem_keyDict layout.closed
    address entries subscript found inside
  simp only [id_eq, relocateValue_id, executed, Option.map_some] at stationary
  have unchanged : after = logical := congrArg Prod.snd (Option.some.inj stationary)
  subst after
  refine ⟨?_, layout, rfl, ?_⟩
  · simpa only [executed, Option.map_some] using
      layout.runtime.getItem_keyDict layout.closed address entries subscript found inside
  · intro returned result
    subst outcome
    exact getItem_keyDict_bounded logical logical layout.closed address entries subscript returned found executed

end FormalSW.PyAst.Mutable.Relocation
