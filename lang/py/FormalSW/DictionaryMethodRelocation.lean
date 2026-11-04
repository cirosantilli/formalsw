import lang.py.FormalSW.ItemWriteRelocation

/-! Optional dictionary lookup separates missing keys from shared stored values. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

/-- Proof normalization of the common lookup performed by get and setdefault. -/
def dictionaryLookup (address : Nat) (key : Value) : Eval (Option Value) := do
  match (← get)[address]? with
  | some (.dict entries) =>
      match key with
      | .scalar scalar => return ScalarDict.lookup entries scalar
      | .ref _ => return HashDict.lookup (promoteDictionary entries) (← hashKey key)
  | some (.keyDict entries) => return HashDict.lookup entries (← hashKey key)
  | none => unsupported
  | some _ => error "TypeError"

theorem dictionaryGet_lookup (heap : Heap) (address : Nat) (key fallback : Value) :
    dictionaryGet address key fallback heap =
      (do let previous ← dictionaryLookup address key; pure (previous.getD fallback) : Eval Value) heap := by
  cases found : heap[address]? with
  | none => simp [dictionaryGet, dictionaryLookup, found, unsupported, eval_bind]
  | some object =>
    cases object with
    | dict entries =>
      cases key with
      | scalar key => simp [dictionaryGet, dictionaryLookup, found, eval_bind]
      | ref address =>
        cases resolved : Mutable.keyOf heap (.ref address) with
        | none => simp [dictionaryGet, dictionaryLookup, found, hashKey, resolved, eval_bind, Except.map]
        | some outcome => cases outcome <;> simp [dictionaryGet, dictionaryLookup, found, hashKey, resolved, eval_bind, Except.map]
    | keyDict entries =>
      cases resolved : Mutable.keyOf heap key with
      | none => simp [dictionaryGet, dictionaryLookup, found, hashKey, resolved, eval_bind, Except.map]
      | some outcome => cases outcome <;> simp [dictionaryGet, dictionaryLookup, found, hashKey, resolved, eval_bind, Except.map]
    | _ => simp [dictionaryGet, dictionaryLookup, found, error, eval_bind]

theorem dictionarySetDefault_lookup (heap : Heap) (address : Nat) (key fallback : Value) :
    dictionarySetDefault address key fallback heap =
      (do let previous ← dictionaryLookup address key
          match previous with
          | some value => pure value
          | none => let _ ← setItem (.ref address) key fallback; pure fallback : Eval Value) heap := by
  cases found : heap[address]? with
  | none => simp [dictionarySetDefault, dictionaryLookup, found, unsupported, eval_bind]
  | some object =>
    cases object with
    | dict entries =>
      cases key with
      | scalar key =>
        cases selected : ScalarDict.lookup entries key <;>
          simp [dictionarySetDefault, dictionaryLookup, setItem, found, selected, eval_bind, Except.map]
      | ref address =>
        cases resolved : Mutable.keyOf heap (.ref address) with
        | none => simp [dictionarySetDefault, dictionaryLookup, found, hashKey, resolved, eval_bind, Except.map]
        | some outcome =>
          cases outcome with
          | error exception => simp [dictionarySetDefault, dictionaryLookup, found, hashKey, resolved, eval_bind, Except.map]
          | ok hashed =>
            cases selected : HashDict.lookup (promoteDictionary entries) hashed <;>
              simp [dictionarySetDefault, dictionaryLookup, setItem, found, hashKey, resolved, selected, eval_bind, Except.map]
    | keyDict entries =>
      cases resolved : Mutable.keyOf heap key with
      | none => simp [dictionarySetDefault, dictionaryLookup, found, hashKey, resolved, eval_bind, Except.map]
      | some outcome =>
        cases outcome with
        | error exception => simp [dictionarySetDefault, dictionaryLookup, found, hashKey, resolved, eval_bind, Except.map]
        | ok hashed =>
          cases selected : HashDict.lookup entries hashed <;>
            simp [dictionarySetDefault, dictionaryLookup, setItem, found, hashKey, resolved, selected, eval_bind, Except.map]
    | _ => simp [dictionarySetDefault, dictionaryLookup, found, error, eval_bind]

theorem RuntimeLayout.dictionaryLookup_relocates {logical physical : Heap} {rename : Nat → Nat}
    (layout : RuntimeLayout logical physical rename) (closed : Closed logical)
    (address : Nat) (key : Value) (addressInside : address < logical.length) (keyInside : key.edge.Within logical.length) :
    dictionaryLookup (rename address) (relocateValue rename key) physical =
      (dictionaryLookup address key logical).map (fun pair => (pair.1.map (Option.map (relocateValue rename)), physical)) := by
  have found : logical[address]? = some logical[address] := List.getElem?_eq_getElem addressInside
  have moved := layout.lookup address _ found
  have resolvedPair := layout.keyOf closed key keyInside
  cases object : logical[address] <;> simp only [object, relocateObject] at moved
  case dict entries =>
    cases key with
    | scalar key =>
      change dictionaryLookup (rename address) (.scalar key) physical = _
      simp [dictionaryLookup, found, object, moved, scalarDict_lookup_relocates, Except.map]
    | ref keyAddress =>
      change dictionaryLookup (rename address) (.ref (rename keyAddress)) physical = _
      simp only [relocateValue] at resolvedPair
      have promoted := promoteDictionary_relocates entries rename
      simp only [relocateHashEntries] at promoted
      cases resolved : Mutable.keyOf logical (.ref keyAddress) with
      | none => simp [dictionaryLookup, found, object, moved, hashKey, resolvedPair, resolved, eval_bind, Except.map]
      | some outcome =>
        cases outcome <;>
          simp [dictionaryLookup, found, object, moved, hashKey, resolvedPair, resolved, eval_bind,
            promoted, hashDict_lookup_relocates, Except.map]
  case keyDict entries =>
    cases resolved : Mutable.keyOf logical key with
    | none => simp [dictionaryLookup, found, object, moved, hashKey, resolvedPair, resolved, eval_bind, Except.map]
    | some outcome =>
      cases outcome <;>
        simp [dictionaryLookup, found, object, moved, hashKey, resolvedPair, resolved, eval_bind,
          hashDict_lookup_relocates, Except.map]
  all_goals simp [dictionaryLookup, found, object, moved, error, Except.map]

theorem dictionaryLookup_effect (heap after : Heap) (closed : Closed heap) (address : Nat) (key : Value)
    (outcome : Except ExceptionObject (Option Value))
    (executed : dictionaryLookup address key heap = some (outcome, after)) :
    after = heap ∧ ∀ value, outcome = .ok (some value) → value.edge.Within heap.length := by
  have hashedLookup (entries : List (HashDict.Entry Value)) (hashed : HashKey)
      (inside : ObjectWithin heap.length (.keyDict entries)) (value : Value)
      (selected : HashDict.lookup entries hashed = some value) : value.edge.Within heap.length := by
    cases found : HashDict.find? entries hashed with
    | none => simp [HashDict.lookup, found] at selected
    | some entry =>
      have same : entry.2.2 = value := by simpa [HashDict.lookup, found] using selected
      rw [← same]
      exact inside entry.2.2 (List.mem_flatMap.mpr ⟨entry, List.mem_of_find?_eq_some found, by simp⟩)
  cases found : heap[address]? with
  | none => simp [dictionaryLookup, found, unsupported] at executed
  | some object =>
    have bounded := closed object (List.mem_of_getElem? found)
    cases object with
    | dict entries =>
      cases key with
      | scalar key =>
        simp [dictionaryLookup, found] at executed
        rcases executed with ⟨rfl, rfl⟩
        refine ⟨rfl, ?_⟩
        intro value success
        exact ScalarDict.lookup_property entries key (fun value => value.edge.Within heap.length)
          (fun entry member => bounded entry.2 (List.mem_map.mpr ⟨entry, member, rfl⟩)) (Except.ok.inj success)
      | ref address =>
        cases resolved : Mutable.keyOf heap (.ref address) with
        | none => simp [dictionaryLookup, found, hashKey, resolved, eval_bind, Except.map] at executed
        | some outcome =>
          cases outcome with
          | error exception =>
            simp [dictionaryLookup, found, hashKey, resolved, eval_bind, Except.map] at executed
            rcases executed with ⟨rfl, rfl⟩
            exact ⟨rfl, by intro _ impossible; cases impossible⟩
          | ok hashed =>
            simp [dictionaryLookup, found, hashKey, resolved, eval_bind, Except.map] at executed
            rcases executed with ⟨rfl, rfl⟩
            exact ⟨rfl, fun value success => hashedLookup _ hashed
              (ObjectWithin.promoteDictionary entries heap.length bounded) value (Except.ok.inj success)⟩
    | keyDict entries =>
      cases resolved : Mutable.keyOf heap key with
      | none => simp [dictionaryLookup, found, hashKey, resolved, eval_bind, Except.map] at executed
      | some outcome =>
        cases outcome with
        | error exception =>
          simp [dictionaryLookup, found, hashKey, resolved, eval_bind, Except.map] at executed
          rcases executed with ⟨rfl, rfl⟩
          exact ⟨rfl, by intro _ impossible; cases impossible⟩
        | ok hashed =>
          simp [dictionaryLookup, found, hashKey, resolved, eval_bind, Except.map] at executed
          rcases executed with ⟨rfl, rfl⟩
          exact ⟨rfl, fun value success => hashedLookup _ hashed bounded value (Except.ok.inj success)⟩
    | _ =>
      simp [dictionaryLookup, found, error] at executed
      rcases executed with ⟨rfl, rfl⟩
      exact ⟨rfl, by intro _ impossible; cases impossible⟩

end FormalSW.PyAst.Mutable.Relocation
