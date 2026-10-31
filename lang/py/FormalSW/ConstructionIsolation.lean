import lang.py.FormalSW.AllocationIsolation
import lang.py.FormalSW.DictionaryConstructionRelocation
import lang.py.FormalSW.SetFromRelocation

/-! Private layouts survive caller mutations and constructors that retain partial allocations on error. -/
namespace FormalSW.PyAst.Mutable.Relocation
set_option Elab.async false

variable {logical physical : Heap} {rename : Nat → Nat} {address : Nat} {object : Object}

/-- The fresh cell may have been filled or partly filled after allocation. -/
theorem PrivateLayout.fresh_extension (before : PrivateLayout logical physical rename address object)
    (after other : Heap)
    (retained : ExecutionLayout after other (extendMap rename logical.length physical.length))
    (size : after.length = logical.length + 1) (saved : SavedCell address object other) :
    PrivateLayout after other (extendMap rename logical.length physical.length) address object := by
  refine ⟨retained, saved, ?_⟩
  rw [size]
  exact extendMap_excludes rename logical.length physical.length address before.excludes
    (List.getElem?_eq_some_iff.mp before.saved).1

/-- A caller write changes its own object while preserving a separate protected object. -/
theorem PrivateLayout.set_nonempty (before : PrivateLayout logical physical rename address object)
    (receiver : Nat) (old updated : Object) (found : logical[receiver]? = some old)
    (oldNotEmpty : old ≠ .tuple []) (newNotEmpty : updated ≠ .tuple [])
    (inside : ObjectWithin logical.length updated) :
    PrivateLayout (logical.set receiver updated)
      (physical.set (rename receiver) (relocateObject rename updated)) rename address object := by
  exact before.preserves _ _ (before.layout.set_nonempty receiver old updated found oldNotEmpty newNotEmpty inside)
    (List.length_set ..)
    (SavedCell.update address (rename receiver) object
      (before.excludes receiver (List.getElem?_eq_some_iff.mp found).1) _ _ before.saved)

/-- A solver may update its own private object between separate caller executions. -/
theorem PrivateLayout.update_private (before : PrivateLayout logical physical rename address object)
    (updated : Object) (oldNotEmpty : object ≠ .tuple []) (newNotEmpty : updated ≠ .tuple []) :
    PrivateLayout logical (physical.set address updated) rename address updated := by
  refine ⟨before.layout.preserves (before.layout.runtime.preserves ?_)
    (emptyTupleAddress_set physical address object updated before.saved oldNotEmpty newNotEmpty), ?_, before.excludes⟩
  · intro source bounded
    exact List.getElem?_set_ne (Ne.symm (before.excludes source bounded))
  · have bound := (List.getElem?_eq_some_iff.mp before.saved).1
    simp [SavedCell, bound]

theorem PrivateLayout.addItem (before : PrivateLayout logical physical rename address object)
    (receiver : Nat) (value : Value) (receiverInside : receiver < logical.length)
    (inside : value.edge.Within logical.length) (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : Mutable.addItem receiver value logical = some (outcome, after)) :
    ∃ other, Mutable.addItem (rename receiver) (relocateValue rename value) physical =
        some (outcome.map (relocateValue rename), other) ∧
      PrivateLayout after other rename address object ∧ after.length = logical.length ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length) := by
  obtain ⟨other, paired, retained, same, bounded⟩ :=
    before.layout.addItem receiver value receiverInside inside outcome after executed
  have saved := Heapq.preserves_addItem (rename receiver) (SavedCell address object)
    (SavedCell.update address (rename receiver) object (before.excludes receiver receiverInside))
    (relocateValue rename value) physical _ other before.saved paired
  exact ⟨other, paired, before.preserves _ _ retained same saved, same, bounded⟩

/-- Earlier successful insertions remain present when a later key raises. -/
theorem PrivateLayout.addItems (before : PrivateLayout logical physical rename address object)
    (items : List Value) (receiver : Nat) (receiverInside : receiver < logical.length)
    (inside : ∀ value ∈ items, value.edge.Within logical.length)
    (outcome : Except ExceptionObject (List Value)) (after : Heap)
    (executed : items.mapM (Mutable.addItem receiver) logical = some (outcome, after)) :
    ∃ other, (items.map (relocateValue rename)).mapM (Mutable.addItem (rename receiver)) physical =
        some (outcome.map (List.map (relocateValue rename)), other) ∧
      PrivateLayout after other rename address object ∧ after.length = logical.length := by
  obtain ⟨other, paired, retained, same⟩ := before.layout.addItems items receiver receiverInside inside outcome after executed
  have saved := Heapq.Preserves.mapM (SavedCell address object) (items.map (relocateValue rename))
    (Mutable.addItem (rename receiver))
    (fun value _ => Heapq.preserves_addItem (rename receiver) _
      (SavedCell.update address (rename receiver) object (before.excludes receiver receiverInside)) value)
    physical _ other before.saved paired
  exact ⟨other, paired, before.preserves _ _ retained same saved, same⟩

theorem PrivateLayout.allocateSetValues (before : PrivateLayout logical physical rename address object)
    (items : List Value) (inside : ∀ value ∈ items, value.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : Mutable.allocateSetValues items logical = some (outcome, after)) :
    let nextMap := extendMap rename logical.length physical.length
    ∃ other, Mutable.allocateSetValues (items.map (relocateValue rename)) physical =
        some (outcome.map (relocateValue nextMap), other) ∧
      PrivateLayout after other nextMap address object ∧ after.length = logical.length + 1 ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length) := by
  dsimp only
  obtain ⟨other, paired, retained, size, bounded⟩ := before.layout.allocateSetValues items inside outcome after executed
  have saved := Heapq.preserves_allocateSetValues (SavedCell address object) (SavedCell.allocates address object)
    (items.map (relocateValue rename)) physical _ other before.saved paired
  exact ⟨other, paired, before.fresh_extension _ _ retained size saved, size, bounded⟩

/-- Acquisition failure leaves the map unchanged; successful acquisition starts a fresh set. -/
theorem PrivateLayout.setFrom (layout : PrivateLayout logical physical rename address object)
    (source : Value) (inside : source.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : Mutable.setFrom source logical = some (outcome, after)) :
    ∃ other nextMap,
      Mutable.setFrom (relocateValue rename source) physical =
        some (outcome.map (relocateValue nextMap), other) ∧
      PrivateLayout after other nextMap address object ∧
      (∀ index < logical.length, nextMap index = rename index) ∧
      logical.length ≤ after.length ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length) := by
  have same := layout.layout.runtime.setSourceItems source inside
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
        (setSourceItems_bounded logical layout.layout.closed source inside items read) _ _ built
      refine ⟨other, extendMap rename logical.length physical.length, ?_, finalLayout,
        fun _ bound => extendMap_old _ _ _ _ bound, by omega, returnedInside⟩
      simpa [setFrom_eq, same, read, eval_bind, Except.map] using otherBuilt

/-- dict(iterable) retains its fresh object even if acquisition or a later row raises. -/
theorem PrivateLayout.dictionaryFromIterable (before : PrivateLayout logical physical rename address object)
    (source : Value) (sourceInside : source.edge.Within logical.length)
    (outcome : Except ExceptionObject Value) (after : Heap)
    (executed : DictionaryConstructor.fromIterable source logical = some (outcome, after)) :
    let nextMap := extendMap rename logical.length physical.length
    ∃ other, DictionaryConstructor.fromIterable (relocateValue rename source) physical =
        some (outcome.map (relocateValue nextMap), other) ∧
      PrivateLayout after other nextMap address object ∧ after.length = logical.length + 1 ∧
      (∀ returned, outcome = .ok returned → returned.edge.Within after.length) := by
  dsimp only
  obtain ⟨result, resultHeap, other, left, right, retained, size, _, bounded⟩ :=
    before.layout.dictionaryFromIterable source sourceInside
  cases result with
  | none => simp only [Option.map_none, executed] at left; cases left
  | some result =>
    simp only [Option.map_some, executed, Option.some.injEq, Prod.mk.injEq] at left
    obtain ⟨rfl, rfl⟩ := left
    simp only [Option.map_some] at right
    have saved := Heapq.preserves_dictionaryFromIterable (SavedCell address object) (SavedCell.allocates address object)
      (relocateValue rename source) physical _ other before.saved right
    exact ⟨other, right, before.fresh_extension _ _ retained size saved, size,
      fun returned success => bounded returned (congrArg some success)⟩

end FormalSW.PyAst.Mutable.Relocation
