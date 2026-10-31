import lang.py.FormalSW.ConstructionRelocation

/-! Builtin set construction retains source representatives across object layouts. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

variable {logical physical : Heap} {rename : Nat → Nat}

/-- The collection phase of the actual builtin set constructor. -/
def setSourceItems (source : Value) : Eval (List Value) := do
  match source with
  | .ref address => match (← get)[address]? with
      | some (.set items) => pure (items.map Value.scalar)
      | some (.keySet items) => pure (items.map Prod.snd)
      | some (.dict entries) => pure (entries.map fun entry => Value.scalar entry.1)
      | some (.keyDict entries) => pure (entries.map fun entry => entry.2.1)
      | some (.instance _ _ _) | some (.dataInstance _ _ _ _ _) | none => unsupported
      | _ => Mutable.sequence source
  | _ => Mutable.sequence source

theorem setFrom_eq (source : Value) : Mutable.setFrom source = (do
    let items ← setSourceItems source
    Mutable.allocateSetValues items : Eval Value) := by
  funext heap
  cases source with
  | scalar scalar => rfl
  | ref address =>
    cases found : heap[address]? with
    | none => simp [Mutable.setFrom, Relocation.setSourceItems, found, eval_bind, unsupported]
    | some object =>
      cases object <;> simp [Mutable.setFrom, Relocation.setSourceItems, found, eval_bind, unsupported]

theorem RuntimeLayout.setSourceItems (layout : RuntimeLayout logical physical rename)
    (source : Value) (inside : source.edge.Within logical.length) :
    setSourceItems (relocateValue rename source) physical =
      (setSourceItems source logical).map
        (fun result => (result.1.map (List.map (relocateValue rename)), physical)) := by
  cases source with
  | scalar scalar =>
    cases scalar <;> simp [Relocation.setSourceItems, Mutable.sequence, relocateValue, error, Except.map,
      List.map_map, Function.comp_def]
  | ref address =>
    have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem inside
    have moved := layout.lookup address _ found
    cases object : logical[address] <;>
      simp only [object, relocateObject] at moved <;>
      simp [Relocation.setSourceItems, Mutable.sequence, relocateValue, found, object, moved, unsupported,
        Except.map, List.map_map, Function.comp_def]

theorem setSourceItems_keeps_heap (heap after : Heap) (source : Value)
    (inside : source.edge.Within heap.length) (outcome : Except ExceptionObject (List Value))
    (executed : setSourceItems source heap = some (outcome, after)) : after = heap := by
  have same := (RuntimeLayout.refl heap).setSourceItems source inside
  simp only [relocateValue_id, executed, Option.map_some] at same
  exact congrArg Prod.snd (Option.some.inj same)

theorem setSourceItems_bounded (heap : Heap) (closed : Closed heap) (source : Value)
    (inside : source.edge.Within heap.length) (items : List Value)
    (executed : setSourceItems source heap = some (.ok items, heap)) :
    ∀ value ∈ items, value.edge.Within heap.length := by
  cases source with
  | scalar scalar =>
    cases scalar with
    | int value | bool value | none => simp [Relocation.setSourceItems, Mutable.sequence, error] at executed
    | string text | bytes bytes =>
      simp [Relocation.setSourceItems, Mutable.sequence] at executed
      subst items
      intro value member
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
      trivial
  | ref address =>
    have found : heap[address]? = some heap[address] := List.getElem?_eq_getElem inside
    generalize objectValue : heap[address] = object at found
    have old := closed object (List.mem_of_getElem? found)
    cases object with
    | list values | tuple values =>
      simp [Relocation.setSourceItems, Mutable.sequence, found] at executed
      subst items
      exact old
    | bytearray bytes | set values | dict entries =>
      simp [Relocation.setSourceItems, Mutable.sequence, found] at executed
      subst items
      intro value member
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
      trivial
    | keySet entries =>
      simp [Relocation.setSourceItems, found] at executed
      subst items
      exact old
    | keyDict entries =>
      simp [Relocation.setSourceItems, found] at executed
      subst items
      intro value member
      obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
      exact old entry.2.1 (List.mem_flatMap.mpr ⟨entry, present, by simp⟩)
    | «instance» origin name fields | dataInstance origin name frozen declared fields =>
      simp [Relocation.setSourceItems, found, unsupported] at executed

/-- Both input rejection and construction errors retain corresponding heaps and outcomes. -/
theorem ExecutionLayout.setFrom (layout : ExecutionLayout logical physical rename)
    (source : Value) (inside : source.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : Mutable.setFrom source logical = some (outcome, after)) :
    ∃ other nextMap,
      Mutable.setFrom (relocateValue rename source) physical =
        some (outcome.map (relocateValue nextMap), other) ∧
      ExecutionLayout after other nextMap ∧
      (∀ index < logical.length, nextMap index = rename index) ∧
      logical.length ≤ after.length ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length) := by
  have same := layout.runtime.setSourceItems source inside
  cases read : setSourceItems source logical with
  | none => simp [setFrom_eq, read, eval_bind] at executed
  | some pair =>
    rcases pair with ⟨result, middle⟩
    have unchanged := setSourceItems_keeps_heap logical middle source inside result read
    subst middle
    cases result with
    | error exception =>
      have matched : some (.error exception, logical) = some (outcome, after) := by
        simpa [setFrom_eq, read, eval_bind] using executed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj matched)
      refine ⟨physical, rename, ?_, layout, fun _ _ => rfl, Nat.le_refl _, ?_⟩
      · simp [setFrom_eq, same, read, eval_bind, Except.map]
      · intro returned impossible
        cases impossible
    | ok items =>
      have built : Mutable.allocateSetValues items logical = some (outcome, after) := by
        simpa [setFrom_eq, read, eval_bind] using executed
      obtain ⟨other, otherBuilt, finalLayout, size, returnedInside⟩ := layout.allocateSetValues items
        (setSourceItems_bounded logical layout.closed source inside items read) _ _ built
      refine ⟨other, extendMap rename logical.length physical.length, ?_, finalLayout,
        fun _ bound => extendMap_old _ _ _ _ bound, by omega, returnedInside⟩
      simpa [setFrom_eq, same, read, eval_bind, Except.map] using otherBuilt

theorem ExecutionLayout.setFrom_unsupported (layout : ExecutionLayout logical physical rename)
    (source : Value) (inside : source.edge.Within logical.length) :
    Mutable.setFrom (relocateValue rename source) physical = none ↔ Mutable.setFrom source logical = none := by
  have same := layout.runtime.setSourceItems source inside
  cases read : setSourceItems source logical with
  | none => simp [setFrom_eq, same, read, eval_bind]
  | some pair =>
    rcases pair with ⟨result, middle⟩
    have unchanged := setSourceItems_keeps_heap logical middle source inside result read
    subst middle
    cases result with
    | error exception => simp [setFrom_eq, same, read, eval_bind, Except.map]
    | ok items =>
      have built := layout.allocateSetValues_unsupported items
        (setSourceItems_bounded logical layout.closed source inside items read)
      simpa [setFrom_eq, same, read, eval_bind, Except.map] using built

end FormalSW.PyAst.Mutable.Relocation
